open import Prelude
open import Cubical.Foundations.HLevels

module Definitions (I : Type) where

IType : Type₁
IType = I → Type

infixr 5 _I→_
_I→_ : IType → IType → IType
(X I→ Y) i = X i → Y i

infixr 5 _i→_
_i→_ : IType → IType → Type
X i→ Y = ∀ (i : I) → (X I→ Y) i

infixl 10 _i»_ 
_i»_ : {A B C : IType} → A i→ B → B i→ C → A i→ C
_i»_ f g i = f i » g i

isISet : IType → Type
isISet X = ∀ i → isSet (X i)

ISet = Σ IType isISet

_IS→_ : ISet → ISet → ISet
(X IS→ Y) .fst = X .fst I→ Y .fst
(X IS→ Y) .snd i = isSet→ (Y .snd i)

_is→_ : ISet → ISet → Type
X is→ Y = X .fst i→ Y .fst

