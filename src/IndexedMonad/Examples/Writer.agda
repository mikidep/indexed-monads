open import Prelude
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.HLevels

module IndexedMonad.Examples.Writer (I : Type) (W : Type) (monstr : MonoidStr W) (issI : isSet I) where

Wmon : Monoid ℓ-zero
Wmon = W , monstr

hom[I,I] : Monoid ℓ-zero
hom[I,I] .fst = I → I
hom[I,I] .snd .MonoidStr.ε = idfun _
hom[I,I] .snd .MonoidStr._·_ f g = f » g
hom[I,I] .snd .MonoidStr.isMonoid .IsMonoid.isSemigroup = issemigroup (isSet→ issI) (λ x y z → refl)
hom[I,I] .snd .MonoidStr.isMonoid .IsMonoid.·IdR x = refl
hom[I,I] .snd .MonoidStr.isMonoid .IsMonoid.·IdL x = refl

IsWIAction : (W → I → I) → Type
IsWIAction = λ act → IsMonoidHom monstr act (hom[I,I] .snd)

open import IndexedContainer I
open IndexedContainer

module _ (_▹_ : W → I → I) (isAct : IsWIAction _▹_) where
  open import Cubical.Data.Unit

  WIC : IndexedContainer
  WIC .S _ = W
  WIC .P {i} w j = w ▹ i ≡ j 

  open import IndexedMonad I WIC
  open IndexedContainer WIC
  open MonoidStr monstr
  open IsMonoidHom isAct

  module _ where
    open RawICMS
    wic-ricms : RawICMS
    wic-ricms .e _ = ε
    wic-ricms ._•_ w w′ = w · w′ refl
    wic-ricms .↑ {i} {s = w} _ = w ▹ i
    wic-ricms .↖ _ = refl
    wic-ricms .↗ {i} {s = w} {s′ = w′} w·w′▹i≡j = sym (pres· w (w′ refl) ≡$ i) ∙ w·w′▹i≡j
    wic-ricms .P-e-idx {i} ε▹i≡j = sym (presε ≡$ i) ∙ ε▹i≡j

  open RawICMS wic-ricms
  open isICMS
  open import Cubical.Foundations.Transport using (isSet-subst)
  open import Cubical.Functions.FunExtEquiv
  wic-isicms : isICMS wic-ricms
  wic-isicms .e-unit-l = ·IdR
  wic-isicms .↖-unit-l w = funExtDep λ _ → issI _ _ _ _ 
  wic-isicms .e-unit-r {i} w = ·IdL _ ∙ substRefl {x = i} w
  wic-isicms .↗-unit-r w  = funExtDep λ _ → issI _ _ _ _
  wic-isicms .•-assoc {i} w w′ w″ = 
    ·Assoc w (w′ refl) (w″ refl refl) 
    ∙ cong ((w · w′ refl) ·_) (cong₂ (λ j x → w″ {j = j} refl x) (sym $ pres· w (w′ refl) ≡$ i) (toPathP (issI _ _ _ _)))
  wic-isicms .↑-↗↑-assoc {i} w w′ w″ = toPathP (funExt λ p → transportRefl (w′ refl ▹ (w ▹ i)) ∙ (sym $ pres· w (w′ refl) ≡$ i))
  wic-isicms .↖↑-↑-assoc {i} w w′ w″ = toPathP (funExt λ p → transportRefl (w ▹ i))
  wic-isicms .↖↖-↖-assoc w w′ w″  = toPathP (funExt λ p → issI _ _ _ _)
  wic-isicms .↖↗-↗↖-assoc w w′ w″ = toPathP (funExt λ p → issI _ _ _ _)
  wic-isicms .↗-↗↗-assoc w w′ w″  = toPathP (funExt λ p → issI _ _ _ _)
