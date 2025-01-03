open import Prelude

module IndexedSetMonads (I : Type) where

open import ISetCat I
open import IndexedSetContainer I
open import Cubical.WildCat.Base

module _ (T : ISetEndo) where
  record RawMonad : Type₁ where
    field
      η : ISetEndoTrans IdEndo T 
      μ : ISetEndoTrans (T ;E T) T 
  
  record isMonad (rawm : RawMonad) : Type₁ where
    open RawMonad rawm
    open WildCat ISetEndoCat
    field
      η-unit-l : {! !} ⋆ ((η ⊳ T) ⋆ μ) ≡ ISetIdTrans T
      η-unit-r : {! !} ⋆ μ ≡ ISetIdTrans T 
      -- μ-assoc : (id₁ T ⊗₁ μ) ; μ ≡ (associator {F = T} ; ((μ ⊗₁ id₁ T) ; μ))
