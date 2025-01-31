open import Prelude
open import Cubical.Categories.Category.Base using (Category; _[_,_])
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Functors.Endo
open import Cubical.Foundations.HLevels

module IndexedSetContainer (I : Type) (issI : isSet I) where

open import Definitions I

open Category

SetI : Category (ℓ-suc ℓ-zero) ℓ-zero
SetI .ob = ISet
SetI .Hom[_,_] X Y = X is→ Y
SetI .id = λ i x → x
SetI ._⋆_ f g i = f i » g i
SetI .⋆IdL _ = refl
SetI .⋆IdR _ = refl
SetI .⋆Assoc _ _ _ = refl
SetI .isSetHom {y} = isSetΠ2 λ i _ → y i .snd

SetIEndo : Category (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
SetIEndo = EndofunctorCategory SetI

open import IndexedContainer I as IC using (IndexedContainer)

record IndexedSetContainer : Type₁ where
  field
    hS : ISet
    hP : {i : I} → hS i .fst → ISet
  ic : IndexedContainer
  ic .IndexedContainer.S i   = hS i .fst
  ic .IndexedContainer.P s j = hP s j .fst

open IndexedSetContainer

_⇒_ : (F G : IndexedSetContainer) → Type
F ⇒ G = ic F IC.⇒ ic G

module _ (F G : IndexedSetContainer) where
  open import Cubical.Foundations.Isomorphism
  isSet-⇒ : isSet (F ⇒ G)
  isSet-⇒ = isSetΠ2 (λ i s → isOfHLevelRespectEquiv 2
      (isoToEquiv (invIso IC.Π⇒IsoΣ)) 
      (isSetΣ (G .hS i .snd) λ _ → isSetImplicitΠ λ _ → isSet→ (F .hP s _ .snd))
    )

ISCCat : Category (ℓ-suc ℓ-zero) ℓ-zero
ISCCat .ob = IndexedSetContainer
ISCCat .Hom[_,_] F G = F ⇒ G
ISCCat .id {x = F} = IC.id₁ (ic F)
ISCCat ._⋆_ = IC._;_
ISCCat .⋆IdL _ = refl
ISCCat .⋆IdR _ = refl
ISCCat .⋆Assoc _ _ _ = refl
ISCCat .isSetHom {x} {y} = isSet-⇒ x y

open Functor

ext-ob : IndexedSetContainer → SetIEndo .ob
ext-ob F .F-ob X i .fst = IC.⟦ ic F ⟧ (itype X) i
ext-ob F .F-ob X i .snd = isSetΣ
  (F .hS i .snd)
  λ s → isSetImplicitΠ λ j → isSet→ (X j .snd)
ext-ob F .F-hom f = ic F IC.⟦$⟧ f
ext-ob F .F-id = refl
ext-ob F .F-seq _ _ = refl

open import Cubical.Categories.NaturalTransformation.Base hiding (_⇒_)
open NatTrans 
open IC._Π⇒_

module _ (F G : IndexedSetContainer)  where
  ext-mor : (F ⇒ G) → SetIEndo [ ext-ob F , ext-ob G ]
  ext-mor α .N-ob = compute 
    where
    compute : (X : ISet) → ext-ob F .F-ob X is→ ext-ob G .F-ob X 
    compute X i (s , v) = α i s .σs , α i s .πs » v
  ext-mor α .N-hom _ = refl

  open import Cubical.Foundations.Isomorphism
  open import Cubical.Functions.FunExtEquiv
  open import Cubical.Foundations.Equiv using (invEq)
  ext-mor-inv : SetIEndo [ ext-ob F , ext-ob G ] → F ⇒ G
  ext-mor-inv α i s = record { σs = repr .fst ; πs = repr .snd }
    where
    open import Cubical.Categories.Yoneda
    ⟦G⟧ : ISet → ISet
    ⟦G⟧ = ext-ob G .F-ob
    -- Endofunctors [ Set^I , Set^I ] can be seen as PSh(Set^I × I),
    -- in this view this is probably good old fashioned Yoneda lemma.
    yo→ :
      (∀ (X : SetI .ob) → (F .hP s is→ X) → ⟦G⟧ X i .fst)
      → ⟦G⟧ (F .hP s) i .fst 
    yo→ nat = nat (F .hP s) (SetI .id {F .hP s})
    repr : ⟦G⟧ (F .hP s) i .fst
    repr = yo→ λ X FP→X → α .N-ob X i (s , (λ {j} → FP→X j))

  iso-ext-mor : Iso (F ⇒ G) (SetIEndo [ ext-ob F , ext-ob G ])
  iso-ext-mor .Iso.fun = ext-mor
  iso-ext-mor .Iso.inv = ext-mor-inv
  iso-ext-mor .Iso.rightInv α = makeNatTransPath
    (funExt₃ λ {
      X i (s , v) →
        let
          α□v = α .N-hom λ j → v {j}
        in 
          sym $ invEq funExt₂Equiv α□v i (s , λ p → p)
     })
  iso-ext-mor .Iso.leftInv α = IC.⇒PathP λ _ → refl

ext : Functor ISCCat SetIEndo
ext .F-ob = ext-ob
ext .F-hom = ext-mor _ _
ext .F-id = makeNatTransPath refl
ext .F-seq _ _ = makeNatTransPath refl

fullyFaithful-ext : isFullyFaithful ext
fullyFaithful-ext F G = isoToIsEquiv (iso-ext-mor F G)
  where open import Cubical.Foundations.Isomorphism

