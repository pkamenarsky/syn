{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Syn where

import Control.Arrow
import Control.Category hiding (id, (.))
import Control.Applicative

import Control.Monad.IO.Class
import Control.Monad.Free
import Control.Monad.Trans.Class

import Data.Machine.MealyT
import Data.Machine.Process
import Data.Void

--------------------------------------------------------------------------------

data SynF v m next
  = View v next
  | Blocked next

  | forall a. Lift (m a) (a -> next)
  | forall a. Finalize (m ()) (Syn v m a) (a -> next)

  | forall u a. Applicative m => MapView (u -> m v) (Syn u m a) (a -> next)
  | forall u a. Applicative m =>  ApViewOr (Syn (u -> m v) m a) (Syn u m a) (a -> next)
  | forall u a. Semigroup a => ApViewAnd (Syn (u -> v) m a) (Syn u m a) (a -> next)

deriving instance Functor (SynF v m)

newtype Syn v m a = Syn { unSyn :: Free (SynF v m) a }
  deriving (Functor, Applicative, Monad)

instance (Applicative m, Monoid v) => Alternative (Syn v m) where
  empty = view' mempty >> forever
  a <|> b = apViewOr (mapView (\v -> (v <>)) a) b

instance (Applicative m, Semigroup v, Semigroup a) => Semigroup (Syn v m a) where
  a <> b = apViewAnd (mapView (\v -> (v <>)) a) b

instance MonadTrans (Syn v) where
  lift m = Syn $ liftF $ Lift m id

mapView, (<$$>) :: Applicative m => (u -> v) -> Syn u m a -> Syn v m a
mapView f syn = Syn $ liftF $ MapView (pure . f) syn id

(<$$>) = mapView
infixl 4 <$$>

mapViewM :: Applicative m => (u -> m v) -> Syn u m a -> Syn v m a
mapViewM f syn = Syn $ liftF $ MapView f syn id

apViewOr, (<**>) :: Applicative m => Syn (u -> v) m a -> Syn u m a -> Syn v m a
apViewOr f syn = Syn $ liftF $ ApViewOr (mapView (fmap pure) f) syn id

(<**>) = apViewOr
infixl 4 <**>

apViewOrM :: Applicative m => Syn (u -> m v) m a -> Syn u m a -> Syn v m a
apViewOrM f syn = Syn $ liftF $ ApViewOr f syn id

apViewAnd :: Semigroup a => Syn (u -> v) m a -> Syn u m a -> Syn v m a
apViewAnd f syn = Syn $ liftF $ ApViewAnd f syn id

forever :: Syn v m a
forever = Syn $ Free $ Blocked $ unSyn forever

view' :: v -> Syn v m ()
view' v = Syn $ liftF $ View v ()

view :: v -> Syn v m a
view v = Syn $ Free $ View v $ unSyn forever

finalize :: m () -> Syn v m a -> Syn v m a
finalize fin s = Syn $ liftF $ Finalize fin s id

unsafeNonBlockingIO :: MonadIO m => IO a -> Syn v m a
unsafeNonBlockingIO io = lift $ liftIO io

blocked :: Syn v m a -> Syn v m a
blocked syn = Syn $ Free $ Blocked $ unSyn syn

--------------------------------------------------------------------------------

data RunF v m next
  = YV v next
  | forall a. YA (m a) (a -> next)
  | YB next
  | YF [m ()] next

deriving instance Functor (RunF v m)

newtype Run v m a = Run { unRun :: Free (RunF v m) a }
  deriving (Functor, Applicative, Monad)

yv :: v -> Run v m ()
yv v = Run $ liftF $ YV v ()

ya :: m a -> Run v m a
ya act = Run $ liftF $ YA act id

yb :: Run v m ()
yb = Run $ liftF $ YB ()

yf :: [m ()] -> Run v m ()
yf fins = Run $ liftF $ YF fins ()

whenJust :: Applicative m => Maybe a -> (a -> m ()) -> m ()
whenJust (Just a) f = f a
whenJust Nothing _ = pure ()

reinterpret :: Monad m => Syn v m a -> Run v m a

reinterpret (Syn (Pure a)) = pure a

reinterpret (Syn (Free (View v next)))   = yv v >> reinterpret (Syn next)
reinterpret (Syn (Free (Blocked next)))  = yb >> reinterpret (Syn next)
reinterpret (Syn (Free (Lift act next))) = ya act >>= reinterpret . Syn . next

reinterpret (Syn (Free (MapView f syn next))) = go (unRun $ reinterpret syn)
  where
    go y = do
      case y of
        Pure a -> reinterpret (Syn $ next a)
        Free (YV v next')  -> ya (f v) >>= yv >> go next'
        Free (YA a next')  -> ya a >>= go . next'
        Free (YB next')    -> yb >> go next'
        Free (YF fs next') -> yf fs >> go next'

reinterpret (Syn (Free (ApViewOr a b next))) = go [] [] (unRun $ reinterpret a) (unRun $ reinterpret b) Nothing Nothing
  where
    go aFins bFins aY bY aPrV bPrV = case (aY, bY) of
      -- finalizers
      (Free (YF fs next'), x) -> yf (fs <> bFins) >> go fs bFins next' x aPrV bPrV
      (x, Free (YF fs next')) -> yf (aFins <> fs) >> go aFins fs x next' aPrV bPrV

      -- actions
      (Free (YA act aNext), x) -> ya act >>= \a' -> go aFins bFins (aNext a') x aPrV bPrV
      (x, Free (YA act bNext)) -> ya act >>= \a' -> go aFins bFins x (bNext a') aPrV bPrV

      -- one finished
      (Pure r, _) -> do
        ya $ sequence_ bFins
        yf []
        reinterpret (Syn $ next r)
      (_, Pure r) -> do
        ya $ sequence_ aFins
        yf []
        reinterpret (Syn $ next r)

      -- both views
      (Free (YV aV aNext), Free (YV bV bNext)) -> do
        ya (aV bV) >>= yv
        go aFins bFins aNext bNext (Just aV) (Just bV)

      -- one view
      (Free (YV aV aNext), Free (YB bNext)) -> do
        whenJust bPrV $ \bV' -> ya (aV bV') >>= yv
        go aFins bFins aNext bNext (Just aV) bPrV

      (Free (YB aNext), Free (YV bV bNext)) -> do
        whenJust aPrV $ \aV' -> ya (aV' bV) >>= yv
        go aFins bFins aNext bNext aPrV (Just bV)

      -- both blocked
      (Free (YB aNext), Free (YB bNext)) -> yb >> go aFins bFins aNext bNext aPrV bPrV
        -- Free (YF fs next') -> yf fs >> go next'

reinterpret (Syn (Free (ApViewAnd a b next))) = go [] [] (unRun $ reinterpret a) (unRun $ reinterpret b) Nothing Nothing
  where
    go aFins bFins aY bY aPrV bPrV = case (aY, bY) of
      -- finalizers
      (Free (YF fs next'), x) -> yf (fs <> bFins) >> go fs bFins next' x aPrV bPrV
      (x, Free (YF fs next')) -> yf (aFins <> fs) >> go aFins fs x next' aPrV bPrV

      -- actions
      (Free (YA act aNext), x) -> ya act >>= \a' -> go aFins bFins (aNext a') x aPrV bPrV
      (x, Free (YA act bNext)) -> ya act >>= \a' -> go aFins bFins x (bNext a') aPrV bPrV

      -- both finished
      (Pure aR, Pure bR) -> reinterpret $ Syn $ next (aR <> bR)

      -- both views
      (Free (YV aV aNext), Free (YV bV bNext)) -> yv (aV bV) >> go aFins bFins aNext bNext (Just aV) (Just bV)

      -- one view
      (Free (YV aV aNext), Free (YB bNext)) -> do
        whenJust bPrV $ \bV' -> yv (aV bV')
        go aFins bFins aNext bNext (Just aV) bPrV
      (Free (YV aV aNext), x@(Pure _))      -> do
        whenJust bPrV $ \bV' -> yv (aV bV')
        go aFins bFins aNext x (Just aV) bPrV

      (Free (YB aNext), Free (YV bV bNext)) -> do
        whenJust aPrV $ \aV' -> yv (aV' bV)
        go aFins bFins aNext bNext aPrV (Just bV)
      (x@(Pure _), Free (YV bV bNext))      -> do
        whenJust aPrV $ \aV' -> yv (aV' bV)
        go aFins bFins x bNext aPrV (Just bV)

      -- both blocked
      (Free (YB aNext), Free (YB bNext)) -> yb >> go aFins bFins aNext bNext aPrV bPrV

      -- one blocked, the other finished
      (Free (YB aNext), x@(Pure _)) -> yb >> go aFins bFins aNext x aPrV bPrV
      (x@(Pure _), Free (YB bNext)) -> yb >> go aFins bFins x bNext aPrV bPrV

reinterpret (Syn (Free (Finalize fin syn next))) = do
  yf [fin]
  go (unRun $ reinterpret syn)
  where
    go y = do
      case y of
        Pure a -> do
          ya fin
          yf []
          reinterpret (Syn $ next a)
        Free (YV v next')  -> yv v >> go next'
        Free (YA a next')  -> ya a >>= go . next'
        Free (YB next')    -> yb >> go next'
        Free (YF fs next') -> yf (fin:fs) >> go next'

unblock :: Monad m => Run v m Void -> m (Run v m Void, Maybe v)
unblock = go [] . unRun
  where
    go _fs y = case y of
        Pure _             -> undefined -- unreachable
        Free (YV v next)   -> pure (Run next, Just v)
        Free (YB next)     -> pure (Run next, Nothing)
        Free (YA act next) -> act >>= go _fs . next
        Free (YF fs next)  -> go fs next

--------------------------------------------------------------------------------

data AF m next = AB next | forall a. AA (m a) (a -> next) | AF [m ()] next

deriving instance Functor (AF m)

newtype A m a = A { unA :: Free (AF m) a }
  deriving (Functor, Applicative, Monad)

newtype SynA m a b = SynA { unSynA :: MealyT (A m) a b }
  deriving (Functor, Applicative, Semigroup, Monoid, Category, Arrow)

synAutoT :: SynA m a b -> ProcessT (A m) a b
synAutoT (SynA mealy) = autoT mealy

synArrM :: (a -> m b) -> SynA m a b
synArrM f = SynA $ MealyT $ \a -> A $ Free $ AA (f a) $ \b -> Pure (b, unSynA $ synArrM f)

pre :: m a -> (a -> SynA m x y) -> SynA m x y
pre act f = SynA $ MealyT $ \x -> A $ Free $ AA act $ \a -> unA $ runMealyT (unSynA (f a)) x

synUpgradeM :: MealyT m a b -> SynA m a b
synUpgradeM (MealyT m) = SynA $ MealyT $ \a -> A $ Free $ AA (m a) $ \b -> Pure $ fmap (unSynA . synUpgradeM) b

toArr :: Applicative m => Run v m Void -> SynA m () v
toArr (Run (Pure _))              = undefined -- unreachable
toArr (Run (Free (YV v next)))    = SynA $ MealyT $ \() -> pure (v, unSynA $ toArr $ Run next)
toArr (Run (Free (YA act next)))  = SynA $ MealyT $ \() -> A $ Free $ AA act $ fmap (unA . ($ ()) . runMealyT . unSynA . toArr . Run) next
toArr (Run (Free (YB next)))      = SynA $ MealyT $ \() -> A $ Free $ AB $ unA $ runMealyT (unSynA $ toArr $ Run next) ()
toArr (Run (Free (YF fins next))) = SynA $ MealyT $ \() -> A $ Free $ AF fins $ unA $ runMealyT (unSynA $ toArr $ Run next) ()

fromArr :: Monad m => SynA m () v -> Syn v m a
fromArr synA = case unA $ runMealyT (unSynA synA) () of
  Pure (v, next)     -> Syn $ Free $ View v $ unSyn $ fromArr $ SynA next
  Free (AB next)     -> Syn $ Free $ Blocked $ unSyn $ fromArr $ SynA $ MealyT $ \() -> A next
  Free (AF fin next) -> Syn $ Free $ Finalize (sequence_ fin) (fromArr $ SynA $ MealyT $ \() -> A next) (\_ -> unSyn $ fromArr $ SynA $ MealyT $ \() -> A next)
  Free (AA act next) -> Syn $ Free $ Lift act $ fmap (unSyn . fromArr . SynA . MealyT . const . A) next
