{-# LANGUAGE PatternSynonyms #-}

module Language.Grammar where

import           Control.Arrow
import           Control.Applicative
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Data            (Data)
import           Data.Foldable        (asum)
import           Data.Map             (Map)
import qualified Data.Map             as M
import           Data.Semigroup
import           Data.Set             (Set)
import qualified Data.Set             as S
import           Prelude              hiding (seq)
import           Language.Inf            (Infinite)
import           Language.Reg            (Reg)
import qualified Language.Reg            as R

type NT = Int

type Rule a = Reg (Either ((), NT) a)

pattern Nonterm :: a -> Reg (Either ((), a) b)
pattern Nonterm x = R.Symbol (Left ((), x))
pattern Term :: b -> Reg (Either ((), a) b)
pattern Term x = R.Symbol (Right x)

data Grammar a = Grammar
  { start :: Rule a
  , rules :: Map NT (Rule a)
  } deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

type IGrammar m a = Infinite m Grammar a

seq :: Grammar a -> Grammar a -> Grammar a
seq (Grammar s rs) (Grammar s' rs') =
  Grammar (s `R.seq` s') (M.unionWith R.alt rs rs')

alt :: Grammar a -> Grammar a -> Grammar a
alt (Grammar s rs) (Grammar s' rs') =
  Grammar (s `R.alt` s') (M.unionWith R.alt rs rs')

abstract :: NT -> Grammar a -> Grammar a
abstract nt (Grammar s rs) =
  Grammar (Nonterm nt) (M.insertWith R.alt nt s rs)

singleton :: a -> Grammar a
singleton a = Grammar (Term a) M.empty

flat :: Rule a -> Grammar a
flat r = Grammar r M.empty

ruleFor :: NT -> Grammar a -> Rule a
ruleFor nt = M.findWithDefault R.Null nt . rules

reverseRules :: Grammar a -> Map NT [(Maybe NT, Rule a)]
reverseRules g = runReader (go $ start g) (Nothing, R.Eps)
  where
    go =
      \case
        R.Seq a b ->
          M.unionWith (++)
            <$> local (second (R.seq b)) (go a)
            <*> local (second (R.seq a)) (go b)
        R.Alt a b -> M.union <$> go a <*> go b
        Nonterm nt -> do
          ctx <- ask
          M.unionWith (++) <$> local (const (Just nt, R.Eps)) (go (ruleFor nt g)) <*>
            pure (M.singleton nt [ctx])
        _ -> pure mempty

nonterminals :: Grammar a -> Set NT
nonterminals (Grammar st rs) =
  S.unions
    ( ruleNonterminals st
    : M.keysSet rs
    : map ruleNonterminals (M.elems rs)
    )

ruleNonterminals :: Rule a -> Set NT
ruleNonterminals  = \case
  R.Seq x y -> ruleNonterminals x `S.union` ruleNonterminals y
  R.Alt x y -> ruleNonterminals x `S.union` ruleNonterminals y
  Nonterm nt -> S.singleton nt
  _ -> S.empty

topologicalOrder :: Grammar a -> [NT]
topologicalOrder g = evalState (topo (start g))  S.empty
  where
    topo :: Rule a -> State (Set NT) [NT]
    topo = \case
      R.Null -> pure []
      R.Eps -> pure []
      R.Seq x y -> (++) <$> topo x <*> topo y
      R.Alt x y -> (++) <$> topo x <*> topo y
      Term _ -> pure []
      Nonterm nt -> gets (nt `elem`) >>= \case
        False -> do
          modify (S.insert nt)
          (nt:) <$> topo (ruleFor nt g)
        True -> pure []

instance Monoid (Grammar a) where
  mempty = Grammar R.Eps M.empty
  mappend = seq

instance Semigroup (Grammar a)

instance Monad Grammar where
  x >>= f = gjoin $ fmap f x
    where
      gjoin (Grammar st rs) =
        uncurry Grammar $
        runState (M.traverseWithKey joinLRule rs >> joinRule st) M.empty
        where
          joinLRule nt r =
            modify . M.unionWith R.alt . M.singleton nt =<< joinRule r
          joinRule = \case
            R.Null -> pure R.Null
            R.Eps -> pure R.Eps
            R.Seq a b -> R.seq <$> joinRule a <*> joinRule b
            R.Alt a b -> R.alt <$> joinRule a <*> joinRule b
            Nonterm nt -> pure $ Nonterm nt
            Term (Grammar st' rs') ->
              modify (M.unionWith R.alt rs') >> pure st'

instance Applicative Grammar where
  pure = singleton
  f <*> x = f >>= (`fmap` x)

-- | The natural choice for an alternative instance is sum where the null
-- grammar is a unit.
instance Alternative Grammar where
  empty = Grammar R.Null M.empty
  (<|>) = alt
