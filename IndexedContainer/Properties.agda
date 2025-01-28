open import Prelude
open import Cubical.Foundations.Equiv using (_≃_)

module IndexedContainer.Properties {I : Type} where

open import IndexedContainer I as IC using (IndexedContainer)

-- interpretation is strong monoidal
module _ (X : I → Type) where
  idᶜ-≃ : ∀ i → IC.⟦ IC.idᶜ ⟧ X i ≃ X i
  idᶜ-≃ i = isoToEquiv idᶜ-iso
    where
    open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
    open Iso
    idᶜ-iso : Iso (IC.⟦ IC.idᶜ ⟧ X i) (X i)
    idᶜ-iso .fun (_ , x) = x refl
    idᶜ-iso .inv x = _ , λ i≡j → subst X i≡j x
    idᶜ-iso .rightInv x = transportRefl x
    idᶜ-iso .leftInv (_ , x) = ΣPathP
      ( refl
      , implicitFunExt λ {j} → funExt λ i≡j
        → J (λ k i≡k → subst X i≡k (x refl) ≡ x i≡k) (substRefl {B = X} (x refl)) i≡j
      )
      where
        open import Cubical.Data.Sigma using (ΣPathP)

module _ (F G : IndexedContainer) (X : I → Type) where
  ⊗-≃ : ∀ i → (IC.⟦ F ⟧ » IC.⟦ G ⟧) X i ≃ IC.⟦ F IC.⊗ G ⟧ X i
  ⊗-≃ i = isoToEquiv ⊗-iso where
    open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
    open Iso
    ⊗-iso : Iso ((IC.⟦ F ⟧ » IC.⟦ G ⟧) X i) (IC.⟦ F IC.⊗ G ⟧ X i)
    ⊗-iso .fun (s , v) = (s , λ p → v p .fst) , λ { (k , p , q) → v p .snd q }
    ⊗-iso .inv ((s , v) , w) = s , λ p → v p , λ q → w (_ , p , q)
    ⊗-iso .rightInv _ = refl
    ⊗-iso .leftInv  _ = refl
