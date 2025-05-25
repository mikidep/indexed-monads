open import Prelude
open import Cubical.Categories.Category.Base using (Category; _[_,_])
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Functors.Endo
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (_×_)

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
SetI .isSetHom {y} = isSetΠ2 λ i _ → y .snd i

SetIEndo : Category (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
SetIEndo = EndofunctorCategory SetI

open import IndexedContainer I

isSetIC : IndexedContainer → Type
isSetIC (S ⊲ P) =
  (∀ {i} → isSet (S i))
  × (∀ {i} {s : S i} {j} → isSet (P s j))

SetIC = Σ[ ic ∈ IndexedContainer ] isSetIC ic

module _ {F : SetIC} {X : ISet} where
  open IndexedContainer (F .fst)

  private
    issic = F .snd

  isISet-⟦-⟧ : isISet (⟦ F .fst ⟧ (X .fst)) 
  isISet-⟦-⟧ i = isSetΣ (issic .fst)
    λ s → isSetImplicitΠ 
    λ _ → isSetΠ 
    λ _ → X .snd _

module _ {F G : SetIC} where
  open IndexedContainer (F .fst)
  open IndexedContainer (G .fst) renaming (S to S′; P to P′)

  private
    issic = F .snd
    issic′ = G .snd

  isSet-⇒ : isSet ((S ⊲ P) ⇒ (S′ ⊲ P′))
  isSet-⇒ = isSetΠ2 (λ i s →  
      isISet-⟦-⟧ {G} {P s , λ _ → issic .snd} i
    )

ISCCat : Category (ℓ-suc ℓ-zero) ℓ-zero
ISCCat .ob = SetIC
ISCCat .Hom[_,_] (F , _) (G , _) = F ⇒ G
ISCCat .id {x = (F , _)} = id₁ F
ISCCat ._⋆_ = _;_
ISCCat .⋆IdL _ = refl
ISCCat .⋆IdR _ = refl
ISCCat .⋆Assoc _ _ _ = refl
ISCCat .isSetHom {x} {y} = isSet-⇒ {x} {y}

open Functor

ext-ob : SetIC → SetIEndo .ob
ext-ob (F , issic) .F-ob (X , iss) = ⟦ F ⟧ X , isISet-⟦-⟧ {F , issic} {X , iss}
ext-ob (F , _) .F-hom f = F ⟦$⟧ f
ext-ob F .F-id = refl
ext-ob F .F-seq _ _ = refl

open import Cubical.Categories.NaturalTransformation.Base hiding (_⇒_)
open NatTrans 

module _ (F G : SetIC)  where
  open IndexedContainer (F .fst)
  open IndexedContainer (G .fst) renaming (S to S′; P to P′)

  private
    issic = F .snd
    issic′ = G .snd

  ext-mor : ISCCat [ F , G ] → SetIEndo [ ext-ob F , ext-ob G ]
  ext-mor α .N-ob X = ⟦⇒⟧ α (X .fst)
  ext-mor α .N-hom _ = refl

  open import Cubical.Foundations.Isomorphism
  open import Cubical.Functions.FunExtEquiv
  open import Cubical.Foundations.Equiv using (invEq)
  ext-mor-inv : SetIEndo [ ext-ob F , ext-ob G ] → ISCCat [ F , G ]
  ext-mor-inv α i s = goal
    where
    open import Cubical.Categories.Yoneda
    ⟦G⟧ : ISet → ISet
    ⟦G⟧ = ext-ob G .F-ob
    Ps : ISet
    Ps = P s , λ _ → issic .snd
    yo→ :
      (∀ (X : ISet) → (Ps is→ X) → ⟦G⟧ X .fst i)
      → ⟦G⟧ Ps .fst i
    yo→ nat = nat Ps (SetI .id {Ps})
    goal : ⟦G⟧ Ps .fst i
    goal = yo→ λ X FP→X → α .N-ob X i (s , (λ {j} → FP→X j))

  iso-ext-mor : Iso (ISCCat [ F , G ]) (SetIEndo [ ext-ob F , ext-ob G ])
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
  iso-ext-mor .Iso.leftInv α = ⇒PathP λ _ _ → refl

ext : Functor ISCCat SetIEndo
ext .F-ob = ext-ob
ext .F-hom = ext-mor _ _
ext .F-id = makeNatTransPath refl
ext .F-seq _ _ = makeNatTransPath refl

fullyFaithful-ext : isFullyFaithful ext
fullyFaithful-ext F G = isoToIsEquiv (iso-ext-mor F G)
  where open import Cubical.Foundations.Isomorphism
