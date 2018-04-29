{-# LANGUAGE PatternSynonyms #-}

module Data.Language.Inf where

import           Control.Monad

-- | When a data structure is "self-similar", it can represent structures that
-- are (potentially) infinite. For example, a list is self-similar because if
-- you place a list at one of its indices, that internal list can be inlined to
-- form a larger overall structure.
-- In general, data structures which a monadic have this self-similarity property:
-- If their element is an instance of the same structure, it can be inlined.
-- This pattern is relevant to formal languages because such languages tend to
-- have this recursive structure.
--
-- Here, we present `Infinite`, a wrapper which allows the user to express the
-- idea that a substructure is an effectful computation which generates more
-- structure. This gives the user control over which parts of their structure
-- are infinite and which are finite.

-- | An infinite version of a self-similar data structure contains either
-- finite elements or monadic computations which produce more structure.
newtype Infinite m f a = Infinite
  { getInfinite :: f (Either (m (Infinite m f a)) a)
  }

-- | Convience patterns for finite and infinite computations.

pattern Fin :: b -> Either a b
pattern Fin a = Right a

pattern Inf :: a -> Either a b
pattern Inf a = Left a

instance (Functor m, Functor f) => Functor (Infinite m f) where
  fmap f (Infinite structure) = Infinite $ fmap (\case
    Inf ac -> Inf (fmap (fmap f) ac)
    Fin x -> Fin (f x)) structure

-- | Generate an infinite version of a structure with a single, given element.
singleton :: Applicative f => a -> Infinite m f a
singleton = Infinite . pure . Fin

-- | Translate a finite structure to an infinite version where each element is
-- finite.
infinite :: Functor f => f a -> Infinite m f a
infinite = Infinite . fmap Fin

-- | Collect the current finite prefix of the structure by replacing infinite
-- elements by a default structure.
finite :: Monad f => f a -> Infinite m f a -> f a
finite def =
    ((\case
       Fin x -> pure x
       Inf _ -> def) =<<) .
  getInfinite

-- | Given an infinite structure, unroll the structure one time by performing
-- the deferred computations.
unroll ::
     (Applicative m, Monad f, Traversable f)
  => Infinite m f a
  -> m (Infinite m f a)
unroll =
  fmap (Infinite . join) .
  traverse
    (\case
       Fin x -> pure (pure (Fin x))
       Inf ac -> getInfinite <$> ac) .
  getInfinite

type IList m a = Infinite m [] a
