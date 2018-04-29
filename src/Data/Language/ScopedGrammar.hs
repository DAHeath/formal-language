{-# LANGUAGE PatternSynonyms #-}

module Data.Language.ScopedGrammar where

import           Control.Applicative
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Data            (Data)
import           Data.IntMap          (IntMap)
import qualified Data.IntMap          as M
import           Data.IntSet          (IntSet)
import qualified Data.IntSet          as S
import           Data.Language.Inf    (Infinite)
import           Data.Language.Reg    (Reg)
import qualified Data.Language.Reg    as R
import           Data.Semigroup
import           Prelude              hiding (null, seq)

-- | A "scoped grammar". This is a context free grammar where each nonterminal
-- symbols has some sort of scoping rule built around it (For example, the
-- nonterminals could potentially be parameterized over a subvocabulary).
--
-- The grammar is parameterized over the set of scopes and the vocabulary.
-- | We represent nonterminals as integers.
type NT = Int

-- | A context free rule is a regular expression where the symbols are either
-- in the vocabulary or are a scope paired with a nonterminal.
type Rule s a = Reg (Either (s, NT) a)

-- | Convenience patterns for recognizing terminals and nonterminals.
pattern Nonterm :: s -> a -> Reg (Either (s, a) b)
pattern Nonterm s x = R.Symbol (Left (s, x))
pattern Term :: b -> Reg (Either a b)
pattern Term x = R.Symbol (Right x)

data Grammar s a = Grammar
  { start :: Rule s a
  , rules :: IntMap (Rule s a)
  } deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

type IGrammar m s a = Infinite m (Grammar s) a

-- | Roughly, the grammar which recognizes strings recognized by the first
-- grammar followed by strings recognized by the second grammar.
-- This is not completely precise, because it is possible that the two grammars
-- share nonterminals.
seq :: Grammar s a -> Grammar s a -> Grammar s a
seq (Grammar s rs) (Grammar s' rs') =
  Grammar (s `R.seq` s') (M.unionWith R.alt rs rs')

-- | Roughly, the grammar which recognizes strings recognized by the first
-- grammar or strings recognized by the second grammar.
-- This is not completely precise, because it is possible that the two grammars
-- share nonterminals.
alt :: Grammar s a -> Grammar s a -> Grammar s a
alt (Grammar s rs) (Grammar s' rs') =
  Grammar (s `R.alt` s') (M.unionWith R.alt rs rs')

-- | Hide the grammar behind a new start rule which is just the provided
-- (scoped) nonterminal symbol.
abstract :: s -> NT -> Grammar s a -> Grammar s a
abstract sc nt (Grammar s rs) =
  Grammar (Nonterm sc nt) (M.insertWith R.alt nt s rs)

-- | The grammar which recognizes exactly the given terminal symbol.
singleton :: a -> Grammar s a
singleton a = Grammar (Term a) M.empty

-- | The grammar which recognizes the same strings as the provided grammar
-- rule.
flat :: Rule s a -> Grammar s a
flat r = Grammar r M.empty

-- | The grammar which recognizes nothing.
null :: Grammar s a
null = Grammar R.Null M.empty

-- | The grammar which only recognizes the empty string.
eps :: Grammar s a
eps = Grammar R.Eps M.empty

-- | Look up the grammar rule that corresponds to the given nonterminal.
-- If the nonterminal is not in the grammar, then the corresponding rule
-- recognizes no strings.
ruleFor :: NT -> Grammar s a -> Rule s a
ruleFor nt = M.findWithDefault R.Null nt . rules

-- | The set of all nonterminals that appear somewhere in the grammar.
nonterminals :: Grammar s a -> IntSet
nonterminals (Grammar st rs) =
  S.unions
    (ruleNonterminals st : M.keysSet rs : map ruleNonterminals (M.elems rs))

-- | The set of nonterminals which appear in the given grammar rule.
ruleNonterminals :: Rule s a -> IntSet
ruleNonterminals =
  \case
    R.Seq x y -> ruleNonterminals x `S.union` ruleNonterminals y
    R.Alt x y -> ruleNonterminals x `S.union` ruleNonterminals y
    Nonterm _ nt -> S.singleton nt
    _ -> S.empty

-- | Find a topological ordering for the nonterminals in the grammar.
topologicalOrder :: Grammar s a -> [NT]
topologicalOrder g = evalState (topo (start g)) S.empty
  where
    topo :: Rule s a -> State IntSet [NT]
    topo =
      \case
        R.Null -> pure []
        R.Eps -> pure []
        R.Seq x y -> (++) <$> topo x <*> topo y
        R.Alt x y -> (++) <$> topo x <*> topo y
        Term _ -> pure []
        Nonterm _ nt ->
          gets (nt `S.member`) >>= \case
            False -> do
              modify (S.insert nt)
              (nt :) <$> topo (ruleFor nt g)
            True -> pure []

-- | There are two reasonable choices for a monoid implementation: eps/seq and
-- null/alt. However, we have chosen eps/seq as the concrete implementation
-- since it more naturally parallels the `Alternative` implementation.
instance Monoid (Grammar s a) where
  mempty = eps
  mappend = seq

-- | Since grammars form a Monoid they form a Semigroup.
instance Semigroup (Grammar s a)

-- | The Monad instance for a grammar combines together the subgrammars and
-- inlines their start rules.
instance Monad (Grammar s) where
  x >>= f = go $ fmap f x
    where
      go (Grammar st rs) =
        uncurry Grammar $
        runState (M.traverseWithKey joinLRule rs >> joinRule st) M.empty
        where
          joinLRule nt r =
            modify . M.unionWith R.alt . M.singleton nt =<< joinRule r
          joinRule =
            \case
              R.Null -> pure R.Null
              R.Eps -> pure R.Eps
              R.Seq a b -> R.seq <$> joinRule a <*> joinRule b
              R.Alt a b -> R.alt <$> joinRule a <*> joinRule b
              Nonterm sc nt -> pure $ Nonterm sc nt
              Term (Grammar st' rs') ->
                modify (M.unionWith R.alt rs') >> pure st'

-- | Since grammars form a Monad they form an applicative.
instance Applicative (Grammar s) where
  pure = singleton
  f <*> x = f >>= (`fmap` x)

-- | The natural choice for an alternative instance is alt where the null
-- grammar is a unit.
instance Alternative (Grammar s) where
  empty = null
  (<|>) = alt
