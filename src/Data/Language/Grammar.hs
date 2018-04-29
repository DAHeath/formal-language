{-# LANGUAGE PatternSynonyms #-}

module Data.Language.Grammar where

import           Control.Monad.Reader
import           Data.Data                   (Data)
import           Data.IntMap                 (IntMap)
import qualified Data.IntMap                 as M
import           Data.Language.Inf           (Infinite)
import           Data.Language.Reg           (Reg)
import qualified Data.Language.Reg           as R
import qualified Data.Language.ScopedGrammar as SG
import           Data.IntSet                 (IntSet)

-- | Context free grammars parameterized over their alphabet.
--
-- Grammars are almost directly implemented in terms of scoped grammars (where
-- the "scope" is chosen to be unit). Therefore, for more documentation look
-- at the implementation of scoped grammars.
type NT = Int

type Rule a = Reg (Either ((), NT) a)

pattern Nonterm :: a -> Reg (Either ((), a) b)
pattern Nonterm x = R.Symbol (Left ((), x))
pattern Term :: b -> Reg (Either ((), a) b)
pattern Term x = R.Symbol (Right x)
pattern Grammar :: Rule a -> IntMap (Rule a) -> Grammar a
pattern Grammar s rs = SG.Grammar s rs

type Grammar a = SG.Grammar () a

type IGrammar m a = Infinite m (SG.Grammar ()) a

seq :: Grammar a -> Grammar a -> Grammar a
seq = SG.seq

alt :: Grammar a -> Grammar a -> Grammar a
alt = SG.alt

abstract :: NT -> Grammar a -> Grammar a
abstract nt (Grammar s rs) = Grammar (Nonterm nt) (M.insertWith R.alt nt s rs)

singleton :: a -> Grammar a
singleton = SG.singleton

flat :: Rule a -> Grammar a
flat = SG.flat

null :: Grammar a
null = SG.null

eps :: Grammar a
eps = SG.eps

ruleFor :: NT -> Grammar a -> Rule a
ruleFor = SG.ruleFor

start :: Grammar a -> Rule a
start = SG.start

rules :: Grammar a -> IntMap (Rule a)
rules = SG.rules

nonterminals :: Grammar a -> IntSet
nonterminals = SG.nonterminals

ruleNonterminals :: Rule a -> IntSet
ruleNonterminals = SG.ruleNonterminals

topologicalOrder :: Grammar a -> [NT]
topologicalOrder = SG.topologicalOrder

-- | Given a grammar, we can construct the context for each nonterminal. That
-- is, the possible partial grammar rules which will appear on either side of
-- the nonterminal.
newtype Context a = Context
  { getContext :: IntMap [(Maybe NT, Rule a, Rule a)]
  } deriving (Show, Read, Eq, Ord, Data)

contextualize :: Grammar a -> Context a
contextualize g = Context $ runReader (go $ start g) (Nothing, R.Eps, R.Eps)
  where
    go =
      \case
        R.Seq a b ->
          M.unionWith (++)
            <$> local (\(nt, cbef, caft) -> (nt, cbef, R.seq b caft)) (go a)
            <*> local (\(nt, cbef, caft) -> (nt, R.seq cbef a, caft)) (go b)
        R.Alt a b -> M.union <$> go a <*> go b
        Nonterm nt -> do
          ctx <- ask
          M.unionWith (++) <$>
            local (const (Just nt, R.Eps, R.Eps)) (go (ruleFor nt g)) <*>
            pure (M.singleton nt [ctx])
        _ -> pure mempty

contextFor :: NT -> Context a -> [(Maybe NT, Rule a, Rule a)]
contextFor nt (Context m) = M.findWithDefault [] nt m
