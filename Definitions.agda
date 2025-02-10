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

ISet : Type₁
ISet = I → hSet ℓ-zero

itype : ISet → IType
itype X i = X i .fst

_IS→_ : ISet → ISet → ISet
(X IS→ Y) i .fst = X i .fst → Y i .fst
(X IS→ Y) i .snd = isSet→ (Y i .snd)

_is→_ : ISet → ISet → Type
X is→ Y = ∀ (i : I) → (X IS→ Y) i .fst

