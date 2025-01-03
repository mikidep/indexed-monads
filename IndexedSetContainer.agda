open import Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

module IndexedSetContainer (I : Type) where

open import Definitions I
open import IndexedContainer I as IC using (IndexedContainer)

record IndexedSetContainer : Type₁ where
  field
    hS : ISet
    hP : {i : I} → hS i .fst → ISet
  ic : IndexedContainer
  ic .IndexedContainer.S i   = hS i .fst
  ic .IndexedContainer.P s j = hP s j .fst

open IndexedSetContainer
open IndexedContainer

_⇒_ : (F G : IndexedSetContainer) → Type
F ⇒ G = ic F IC.⇒ ic G

open import Cubical.WildCat.Base
open import WildCat.Functor using (WildFunctor; WildNatTrans)
open WildCat

ISCCat : WildCat (ℓ-suc ℓ-zero) ℓ-zero
ISCCat .ob = IndexedSetContainer
ISCCat .Hom[_,_] F G = F ⇒ G
ISCCat .id {x = F} = IC.id₁ (ic F)
ISCCat ._⋆_ = IC._;_
ISCCat .⋆IdL _ = refl
ISCCat .⋆IdR _ = refl
ISCCat .⋆Assoc _ _ _ = refl

ISCCat[_,_] = ISCCat .Hom[_,_]

open import ISetCat I
open WildFunctor

module _ (F : IndexedSetContainer) where
  interp-ic : ISetEndo
  interp-ic .F-ob X i .fst = IC.⟦ ic F ⟧ (itype X) i
  interp-ic .F-ob X i .snd = isSetΣ
    (F .hS i .snd)
    λ s → isSetImplicitΠ λ j → isSet→ (X j .snd)
  interp-ic .F-hom f = ic F IC.⟦$⟧ f
  interp-ic .F-id = refl
  interp-ic .F-seq _ _ = refl

module _ (F G : IndexedSetContainer) (α : F ⇒ G) where
  open import Cubical.Functions.FunExtEquiv using (funExt₂)
  open import Cubical.Data.Sigma using (ΣPathP)
  open WildNatTrans

  interp-trans : ISetEndoTrans (interp-ic F) (interp-ic G)
  interp-trans .N-ob = compute
    where
    open IC._Π⇒_
    compute : (X : ISet) → interp-ic F .F-ob X is→ interp-ic G .F-ob X 
    compute X i (s , v) = α i s .σs , α i s .πs » v
  interp-trans .N-hom f = refl

module _ (F G : IndexedSetContainer) (α : ISetEndoTrans (interp-ic F) (interp-ic G)) where
  open WildNatTrans
  open IC._Π⇒_
  private
    module _ {i : I} (s : ic F .S i) where
      ⟦G⟧ : ISet → ISet
      ⟦G⟧ = interp-ic G .F-ob
      yoneda : (∀ (X : ISet) → (F .hP s is→ X) → ⟦G⟧ X i .fst) → ⟦G⟧ (F .hP s) i .fst 
      yoneda nat = nat (F .hP s) (ISetCat .WildCat.id {F .hP s})
      yoneda-α : ⟦G⟧ (F .hP s) i .fst 
      yoneda-α = yoneda λ X FP→X → α .N-ob X i (s , λ {j} → FP→X j)

  interp-trans-inv : F ⇒ G
  interp-trans-inv i s .σs = yoneda-α s .fst
  interp-trans-inv i s .πs = yoneda-α s .snd

interpF : WildFunctor ISCCat ISetEndoCat
interpF .F-ob = interp-ic
interpF .F-hom {x = F} {y = G} α = interp-trans F G α
interpF .F-id = ISetEndoTransPathP refl
interpF .F-seq f g = ISetEndoTransPathP refl

fully-faithful-interpF :
  (F G : IndexedSetContainer)
  → F ⇒ G ≃ ISetEndoCat .Hom[_,_] (interp-ic F) (interp-ic G)
fully-faithful-interpF F G = isoToEquiv iso
  where
  open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
  open import Cubical.Foundations.Equiv using (invEq)
  open import Cubical.Functions.FunExtEquiv using (funExt₃; funExt₂Equiv)
  open Iso
  open IC._Π⇒_
  open WildNatTrans
  iso : Iso (F ⇒ G) (ISetEndoCat .Hom[_,_] (interp-ic F) (interp-ic G))
  iso .fun = interp-trans F G
  iso .inv = interp-trans-inv F G
  iso .rightInv α = ISetEndoTransPathP $ funExt₃ λ {
      X i (s , v) → 
        let
          α□v = α .N-hom {x = F .hP s} {y = X} λ j → v {j}
        in 
          sym $ invEq funExt₂Equiv α□v i (s , λ p → p)
    }
  iso .leftInv α = IC.⇒PathP λ s → IC.Π⇒PathP refl refl
