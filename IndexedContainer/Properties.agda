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

module _ where
  open import Cubical.Functions.FunExtEquiv using (funExt₂; funExt₂Equiv)
  open import Cubical.Foundations.Function using (curry; uncurry)
  open import Cubical.Foundations.Equiv

  open import Cubical.WildCat.Base
  open import Cubical.WildCat.BraidedSymmetricMonoidal 
  open import WildCat.Functor
  open WildCat
  open WildFunctor
  open WildNatTrans

  ITypeCat : WildCat (ℓ-suc ℓ-zero) ℓ-zero
  ITypeCat .ob = IType
  ITypeCat .Hom[_,_] = _i→_
  ITypeCat .id = λ i x → x
  ITypeCat ._⋆_ f g i = f i » g i
  ITypeCat .⋆IdL _ = refl
  ITypeCat .⋆IdR _ = refl
  ITypeCat .⋆Assoc _ _ _ = refl

  ICCat : WildCat (ℓ-suc ℓ-zero) ℓ-zero
  ICCat .ob = IndexedContainer
  ICCat .Hom[_,_] F G = F IC.⇒ G
  ICCat .id {x = F} = IC.id₁ F
  ICCat ._⋆_ = IC._;_
  ICCat .⋆IdL _ = refl
  ICCat .⋆IdR _ = refl
  ICCat .⋆Assoc _ _ _ = refl
  
  -- interpretation is full and faithful
  module _ (ic : IndexedContainer) where
    interp-ob : WildFunctor ISetCat ISetCat
    interp-ob .F-ob X .IT = IC.⟦ ic ⟧ (X .IT)
    interp-ob .F-ob X .isSetIT = {! !}
    interp-ob .F-hom = {! !}
    interp-ob .F-id = {! !}
    interp-ob .F-seq = {! !}
