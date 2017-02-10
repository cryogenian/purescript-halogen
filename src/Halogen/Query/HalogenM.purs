module Halogen.Query.HalogenM where

import Prelude

import Control.Applicative.Free (FreeAp, liftFreeAp, hoistFreeAp)
import Control.Monad.Aff.Class (class MonadAff, liftAff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Eff.Exception (Error)
import Control.Monad.Fork (class MonadFork)
import Control.Monad.Free (Free, hoistFree, liftF)
import Control.Monad.Reader.Class (class MonadAsk, ask)
import Control.Monad.Rec.Class (class MonadRec, tailRecM, Step(..))
import Control.Monad.State.Class (class MonadState)
import Control.Monad.Writer.Class (class MonadTell, tell)
import Control.Parallel.Class (class Parallel)

import Data.Bifunctor (lmap)
import Data.Coyoneda (Coyoneda, coyoneda)
import Data.Foreign (Foreign)
import Data.List as L
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype, over)
import Data.Tuple (Tuple)

import Halogen.Query.EventSource as ES
import Halogen.Query.ForkF as FF
import Halogen.Query.InputF (RefLabel)

import Unsafe.Coerce (unsafeCoerce)

class RowEquals (a :: # *) (b :: # *) | a -> b, b -> a where
  toR :: forall p. p a -> p b
  fromR :: forall p. p b -> p a

instance reflR :: RowEquals r r where
  toR = id
  fromR = id

-- | This is used internally to coerce multiple data structures from
-- | `D a b c` to `D' (a :: a, b :: b)`
class TypeEqualsInternal a b | a -> b, b -> a where
  to :: a -> b
  from :: b -> a

data QueryRow (f :: * -> *)
data EffectRow (f :: * -> *)
data ViewRow (f :: * -> * -> *)


-- | The Halogen component algebra
data HalogenF s (f :: * -> *) g p o m (r :: # *) a
  = GetState (s -> a)
  | ModifyState (s -> Tuple a s)
  | Subscribe (ES.EventSource f m) a
  | Lift (m a)
  | Halt String
  | GetSlots (L.List p -> a)
  | CheckSlot p (Boolean -> a)
  | ChildQuery p (Coyoneda g a)
  | Raise o a
  | Par (HalogenAp s f g p o m r a)
  | Fork (FF.Fork (Free (HalogenF s f g p o m r)) a)
  | GetRef RefLabel (Maybe Foreign -> a)

instance functorHalogenF :: Functor m => Functor (HalogenF s f g p o m r) where
  map f = case _ of
    GetState k -> GetState (f <<< k)
    ModifyState k -> ModifyState (lmap f <<< k)
    Subscribe es a -> Subscribe es (f a)
    Lift q -> Lift (map f q)
    Halt msg -> Halt msg
    CheckSlot p k -> CheckSlot p (map f k)
    GetSlots k -> GetSlots (map f k)
    ChildQuery p cq -> ChildQuery p (map f cq)
    Raise o a -> Raise o (f a)
    Par pa -> Par (map f pa)
    Fork fa -> Fork (map f fa)
    GetRef p k -> GetRef p (map f k)

newtype HalogenAp s f g p o m r a  =
  HalogenAp (FreeAp (Free (HalogenF s f g p o m r)) a)


derive instance newtypeHalogenAp :: Newtype (HalogenAp s f g p o m r a) _
derive newtype instance functorHalogenAp :: Functor (HalogenAp s f g p o m r)
derive newtype instance applyHalogenAp :: Apply (HalogenAp s f g p o m r)
derive newtype instance applicativeHalogenAp :: Applicative (HalogenAp s f g p o m r)

data HalogenM (r :: # *) a

instance halogenMISEqualFree
  :: RowEquals r ( state :: s
                 , query :: QueryRow f
                 , childQuery :: QueryRow g
                 , childSlot :: p
                 , output :: o
                 , effect :: EffectRow m
                 | rr)
  => TypeEqualsInternal (HalogenM r a) (Free (HalogenF s f g p o m rr) a) where
  to = unsafeCoerce
  from = unsafeCoerce

instance functorHalogenM
  :: RowEquals r ( state :: s
                 , query :: QueryRow f
                 , childQuery :: QueryRow g
                 , childSlot :: p
                 , output :: o
                 , effect :: EffectRow m
                 | rr)
  => Functor (HalogenM r) where
  map f hm = from $ map f $ to hm

instance applyHalogenM
  :: RowEquals r ( state :: s
                 , query :: QueryRow f
                 , childQuery :: QueryRow g
                 , childSlot :: p
                 , output :: o
                 , effect :: EffectRow m
                 | rr)
  => Apply (HalogenM r) where
  apply f w = from $ apply (to f) (to w)

instance applicativeHalogenM
  :: RowEquals r ( state :: s
                 , query :: QueryRow f
                 , childQuery :: QueryRow g
                 , childSlot :: p
                 , output :: o
                 , effect :: EffectRow m
                 | rr )
  => Applicative (HalogenM r) where
  pure a = from $ pure a

instance bindHalogenM
  :: RowEquals r ( state :: s
                 , query :: QueryRow f
                 , childQuery :: QueryRow g
                 , childSlot :: p
                 , output :: o
                 , effect :: EffectRow m
                 | rr )
  => Bind (HalogenM r) where
  bind rfa rf = from $ to rfa >>= \x -> to $ rf x

instance monadHalogenM
  :: RowEquals r ( state :: s
                 , query :: QueryRow f
                 , childQuery :: QueryRow g
                 , childSlot :: p
                 , output :: o
                 , effect :: EffectRow m
                 | rr )
  => Monad (HalogenM r)

instance monadEffHalogenM
  :: ( RowEquals r ( state :: s
                   , query :: QueryRow f
                   , childQuery :: QueryRow g
                   , childSlot :: p
                   , output :: o
                   , effect :: EffectRow m
                   | rr )
     , MonadEff eff m)
  => MonadEff eff (HalogenM r) where
  liftEff eff = from $ liftF $ Lift $ liftEff eff


instance monadAffHalogenM
  :: ( RowEquals r ( state :: s
                   , query :: QueryRow f
                   , childQuery :: QueryRow g
                   , childSlot :: p
                   , output :: o
                   , effect :: EffectRow m
                   | rr )
     , MonadAff eff m)
  => MonadAff eff (HalogenM r) where
  liftAff aff = from $ liftF $ Lift $ liftAff aff

-- TODO: for some reason it's broken -_-
instance parallelHalogenM
  :: RowEquals r ( state :: s
                 , query :: QueryRow f
                 , childQuery :: QueryRow g
                 , childSlot :: p
                 , output :: o
                 , effect :: EffectRow m
                 | rr)
  => Parallel (HalogenAp s f g p o m rr) (HalogenM r) where
  parallel = HalogenAp <<< liftFreeAp <<< to
  sequential = from <<< liftF <<< Par


instance monadForkHalogenM
  :: ( RowEquals r ( state :: s
                   , query :: QueryRow f
                   , childQuery :: QueryRow g
                   , childSlot :: p
                   , output :: o
                   , effect :: EffectRow m
                   | rr )
     , MonadAff eff m)
  => MonadFork Error (HalogenM r) where
  fork a = map liftAff <$> (from $ liftF $ Fork $ FF.fork $ to a)


instance monadRecHalogenM
  :: RowEquals r ( state :: s
                 , query :: QueryRow f
                 , childQuery :: QueryRow g
                 , childSlot :: p
                 , output :: o
                 , effect :: EffectRow m
                 | rr )
  => MonadRec (HalogenM r) where
  tailRecM k a = k a >>= case _ of
    Loop x -> tailRecM k x
    Done y -> pure y


instance monadStateHalogenM
  :: RowEquals r ( state :: s
                 , query :: QueryRow f
                 , childQuery :: QueryRow g
                 , childSlot :: p
                 , output :: o
                 , effect :: EffectRow m
                 | rr )
  => MonadState s (HalogenM r) where
  state = from <<< liftF <<< ModifyState

instance monadAskHalogenM
  :: ( RowEquals r ( state :: s
                   , query :: QueryRow f
                   , childQuery :: QueryRow g
                   , childSlot :: p
                   , output :: o
                   , effect :: EffectRow m
                   | rr )
     , MonadAsk a m )
  => MonadAsk a (HalogenM r) where
  ask = from $ liftF $ Lift $ ask

instance monadTellHalogenM
  :: ( RowEquals r ( state :: s
                   , query :: QueryRow f
                   , childQuery :: QueryRow g
                   , childSlot :: p
                   , output :: o
                   , effect :: EffectRow m
                   | rr )
     , MonadTell w m)
  => MonadTell w (HalogenM r) where
  tell = from <<< liftF <<< Lift <<< tell

lift
  :: forall s f g p o m r a
   . Monad m
  => m a
  -> HalogenM ( state :: s
              , query :: QueryRow f
              , childQuery :: QueryRow g
              , childSlot :: p
              , output :: o
              , effect :: EffectRow m|r) a
lift m = from $ liftF $ Lift m


halt
  :: forall s f g p o m a r
   . String
  -> HalogenM ( state :: s
              , query :: QueryRow f
              , childQuery :: QueryRow g
              , childSlot :: p
              , output :: o
              , effect :: EffectRow m|r) a
halt msg = from $ liftF $ Halt msg

mkQuery
  :: forall s f g p o m a r
   . Eq p
  => p
  -> g a
  -> HalogenM ( state :: s
              , query :: QueryRow f
              , childQuery :: QueryRow g
              , childSlot :: p
              , output :: o
              , effect :: EffectRow m|r) a
mkQuery p = from <<< liftF <<< ChildQuery p <<< coyoneda id

getSlots
  :: forall s f g p o m r
   . HalogenM ( state :: s
              , query :: QueryRow f
              , childQuery :: QueryRow g
              , childSlot :: p
              , output :: o
              , effect :: EffectRow m|r) (L.List p)
getSlots = from $ liftF $ GetSlots id

checkSlot
  :: forall s f g p o m r
   . p
  -> HalogenM ( state :: s
              , query :: QueryRow f
              , childQuery :: QueryRow g
              , childSlot :: p
              , output :: o
              , effect :: EffectRow m|r) Boolean
checkSlot p = from $ liftF $ CheckSlot p id

getRef
  :: forall s f g p o m r
   . RefLabel
  -> HalogenM ( state :: s
              , query :: QueryRow f
              , childQuery :: QueryRow g
              , childSlot :: p
              , output :: o
              , effect :: EffectRow m|r) (Maybe Foreign)
getRef p = from $ liftF $ GetRef p id

-- | Provides a way of having a component subscribe to an `EventSource` from
-- | within an `Eval` function.
subscribe
  :: forall s f g p o m r
   . ES.EventSource f m
  -> HalogenM ( state :: s
              , query :: QueryRow f
              , childQuery :: QueryRow g
              , childSlot :: p
              , output :: o
              , effect :: EffectRow m|r) Unit
subscribe es = from $ liftF $ Subscribe es unit

-- | Raises an output message for the component.
raise
  :: forall s f g p o m r
   . o
  -> HalogenM ( state :: s
              , query :: QueryRow f
              , childQuery :: QueryRow g
              , childSlot :: p
              , output :: o
              , effect :: EffectRow m |r) Unit
raise o = from $ liftF $ Raise o unit

hoist
  :: forall s f g p o m m' r
   . Functor m'
  => (m ~> m')
  -> HalogenM ( state :: s
              , query :: QueryRow f
              , childQuery :: QueryRow g
              , childSlot :: p
              , output :: o
              , effect :: EffectRow m|r)
  ~> HalogenM ( state :: s
              , query :: QueryRow f
              , childQuery :: QueryRow g
              , childSlot :: p
              , output :: o
              , effect :: EffectRow m'|r)
hoist nat hal = from $ hoistFree go $ to hal
  where
  go ∷ HalogenF s f g p o m r ~> HalogenF s f g p o m' r
  go = case _ of
    GetState k -> GetState k
    ModifyState f -> ModifyState f
    Subscribe es next -> Subscribe (ES.hoist nat es) next
    Lift q -> Lift (nat q)
    GetSlots k -> GetSlots k
    CheckSlot p k -> CheckSlot p k
    ChildQuery p cq -> ChildQuery p cq
    Raise o a -> Raise o a
    Par p -> Par (over HalogenAp (hoistFreeAp (hoistFree go)) p)
    Fork f -> Fork (FF.hoistFork (hoistFree go) f)
    GetRef p k -> GetRef p k
    Halt msg -> Halt msg
