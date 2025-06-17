open import Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Sigma using (_×_)

module IndexedContainer.Properties {I : Type} where

open import Definitions I
open import IndexedContainer I as IC using (IndexedContainer; _⊲_; ⟦_⟧; _⇒_; _;_)
open import IndexedContainer.MonoidalCategory {I}

-- interpretation is strong monoidal
module StrongMonoidal where
  open import IndexedContainer.MonoidalCategory {I} using (idᶜ-≃) public

  module _ (F G : IndexedContainer) (X : I → Type) where
   ⊗-≃ : ∀ i → (⟦ F ⟧ » ⟦ G ⟧) X i ≃ ⟦ F ⊗ G ⟧ X i
   ⊗-≃ i = isoToEquiv ⊗-iso where
     open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
     open Iso
     ⊗-iso : Iso ((⟦ F ⟧ » ⟦ G ⟧) X i) (⟦ F ⊗ G ⟧ X i)
     ⊗-iso .fun (s , v) = (s , λ p → v p .fst) , λ { (k , p , q) → v p .snd q }
     ⊗-iso .inv ((s , v) , w) = s , λ p → v p , λ q → w (_ , p , q)
     ⊗-iso .rightInv _ = refl
     ⊗-iso .leftInv  _ = refl

open StrongMonoidal public


-- ICs are fibered over their shapes
module Fibration where
  module _ {S S′ : IType}
    {P : ∀ {i} → S i → IType}
    {P′ : ∀ {i} → S′ i → IType}
    (α : S ⊲ P ⇒ S′ ⊲ P′)
    where

    σ : S i→ S′
    σ i s = α i s .fst
    
    π : ∀ {i} (s : S i) {j} → P′ (σ i s) j → P s j
    π s = α _ s .snd

  module _
    {S : IType}
    {P : {i : I} → S i → (j : I) → Type}
    where

    ∫ : I → I → Type
    ∫ i j = Σ[ s ∈ S i ] P s j

  module _
    {S : IType}
    {P P′ : {i : I} → S i → (j : I) → Type}
    (α : (S ⊲ P) ⇒ (S ⊲ P′)) where
    isVertical : Type
    isVertical = ∀ i → α i » fst ≡ idfun _

  module _
    {S S′ : IType}
    (σ : S i→ S′)
    (P′ : ∀ {i} → S′ i → IType)
    where

    _* : 
      ∀ {i} → S i → IType
    _* s = P′ (σ _ s)

    -- Do we have to factor through σ(S)??
    lift* :
      S ⊲ _* ⇒ S′ ⊲ P′
    lift* i s = σ i s , idfun _

module Isomorphism {F G : IndexedContainer} where
  open IC
  open IndexedContainer F
  open IndexedContainer G renaming (S to S′; P to P′)
  
  record ⇒Inv (to : F ⇒ G) : Type where
    field
      from : G ⇒ F
      to-from : to ; from ≡ id₁ F
      from-to : from ; to ≡ id₁ G

  record ⇒Iso : Type where
    field
      to   : F ⇒ G
      ⇒inv : ⇒Inv to

  open Fibration
  open import Cubical.Foundations.Equiv
  module _ (α : F ⇒ G)
    (isEquiv-σ : ∀ {i} → isEquiv (σ α i)) 
    (isEquiv-π : ∀ {i} (s : S i) j → isEquiv (π α s {j}))
    where

    open import Cubical.Foundations.Isomorphism

    module _ (i : I) where
      σ-iso : Iso _ _
      σ-iso = equivToIso (σ α i , isEquiv-σ)

      open Iso (σ-iso) using () renaming (inv to σinv)
        public

    σ⌝ = lift* (σ α) P′ 
    σinv⌝ = lift* σinv P 

    module _ {i} (s : S i) (j : I) where
      π-iso : Iso _ _
      π-iso = equivToIso (π α s {j} , isEquiv-π s j)

      open Iso (π-iso) using () renaming (inv to πinv)
        public

    -- vertInv : S′ ⊲ P′ ⇒ S′ ⊲ (σinv *) P
    -- vertInv i s′ = s′ , λ { p → {! !} }
    --
    -- open ⇒Inv
    -- ⇒Iso-≃ : ⇒Inv α
    -- ⇒Iso-≃ .from = vertInv ; σinv⌝
    -- ⇒Iso-≃ .to-from = ⇒PathP {! !}
    -- ⇒Iso-≃ .from-to = {! !}
    
