open import Prelude
import IndexedContainer as IC

module IndexedMonad.Examples.FreeMonad {I : Type} (ic : IC.IndexedContainer I) where

open import IndexedContainer I
open IndexedContainer ic

data S* (i : I) : Type where
  η : S* i
  sup : ⟦ ic ⟧ S* i → S* i

P* : ∀ {i} → S* i → I → Type
P* {i} η j = i ≡ j
P* (sup (s , ps)) j = Σ[ k ∈ I ] Σ[ p ∈ P s k ] P* (ps p) j

FM : IndexedContainer
FM = record { S = S* ; P = P* }

FM-ricms-• : ∀ {i} (s : S* i) → ({j : I} → P* s j → S* j) → S* i
FM-ricms-• η v = v refl
FM-ricms-• (sup (s , ps*)) v = sup (s , λ {j} p → FM-ricms-• (ps* p) λ p* → v (j , p , p*))

FM-ricms-↑ : ∀ {i} 
  (s : S* i) 
  (s′ : {j : I} → P* s j → S* j) 
  {j} 
  → P* (FM-ricms-• s s′) j 
  → I
FM-ricms-↑ {i} η _ _ = i
FM-ricms-↑ (sup (s , ps*)) s′ {j} (k , p , q) = FM-ricms-↑ (ps* p) (λ p* → s′ (k , p , p*)) q

FM-ricms-↖ : ∀ {i} 
  (s : S* i) 
  (s′ : {j : I} → P* s j → S* j) 
  {j} 
  (p : P* (FM-ricms-• s s′) j) 
  → P* s (FM-ricms-↑ s s′ p) 
FM-ricms-↖ η _ _ = refl
FM-ricms-↖ (sup (s , ps*)) s′ (k , p , q) = 
  k , p , FM-ricms-↖ (ps* p) (λ p* → s′ (k , p , p*)) q

FM-ricms-↗ : ∀ {i} 
  (s : S* i) 
  (s′ : {j : I} → P* s j → S* j) 
  {j} 
  (p : P* (FM-ricms-• s s′) j) 
  → P* (s′ (FM-ricms-↖ s s′ p)) j 
FM-ricms-↗ η s′ p = p
FM-ricms-↗ (sup (s , ps*)) s′ (k , p , q) = 
  FM-ricms-↗ (ps* p) (λ p* → s′ (k , p , p*)) q

open import IndexedMonad _ FM

module _ where
  open RawICMS

  FM-ricms : RawICMS
  FM-ricms .e i = η
  FM-ricms ._•_ = FM-ricms-•
  FM-ricms ._↑_ {s} = FM-ricms-↑ s
  FM-ricms ._↖_ {s} = FM-ricms-↖ s
  FM-ricms ._↗_ {s} = FM-ricms-↗ s
  FM-ricms .P-e-idx = idfun _

open isICMS′
open import Cubical.Data.Sigma using (ΣPathP)

private
  open RawICMS FM-ricms
  FM-isicms-e-unit-l : ∀ {i} (s : S* i) → FM-ricms-• s (λ _ → η) ≡ s
  FM-isicms-e-unit-l η = refl
  FM-isicms-e-unit-l (sup (s , ps*)) =
    cong sup
    $ cong (s ,_) 
    $ implicitFunExt
    $ funExt (ps* » FM-isicms-e-unit-l)

  FM-isicms-↖-unit-l : ∀ {i} (s : S* i) {j : I}
    → (p : P* (FM-ricms-• s (λ _ → η)) j) 
    → PathP (λ ι → P* (FM-isicms-e-unit-l s (~ ι)) (FM-ricms-↗ s (λ _ → η) p ι)) (FM-ricms-↖ s (λ _ → η) p) p
  FM-isicms-↖-unit-l η p = λ ι κ → p (ι ∧ κ)
  FM-isicms-↖-unit-l (sup (s , ps*)) (k , p , q) = ΣPathP (refl , ΣPathP (refl , FM-isicms-↖-unit-l (ps* p) q))

  FM-isicms-↗-unit-r′ : ∀ {i} (s : S* i) {j : I}
    (p : P* s j)
    → PathP
      (λ ι → P* s j)
      p p
  FM-isicms-↗-unit-r′ {i} s {j} p = refl

  FM-isicms-↗-unit-r : ∀ {i} (s : S* i) {j : I}
    (p : P* (subst S* refl s) j)
    → PathP
      (λ ι → P* (substRefl {B = S*} (substRefl {B = S*} s ι) (~ ι)) j)
      p p

  -- FM-isicms-↗-unit-r s p = {!   !}

  FM-isicms-↗-unit-r {i} s {j} p = toPathP
    (cong (λ s≡s → subst (λ s → P* s j) s≡s p) aux ∙ substRefl {B = λ s → P* s j} p)
    where
    open import Cubical.Foundations.Path
    aux : (λ ι → transp (λ _ → S* i) (~ ι) (transp (λ _ → S* i) ι s)) ≡ refl
    aux κ ι = {!transp (λ _ → S* i) (~ ι) (transp (λ _ → S* i) (ι) s)!}

  FM-isicms-•-assoc : ∀ {i}
      (s : S* i) (s′ : {j : I} → P* s j → S* j)
      (s″ : {j k : I} (p : P* s k) → P* (s′ p) j → S* j) →
      FM-ricms-• (FM-ricms-• s s′) (smoosh {s = s} s″) ≡
      FM-ricms-• s (_Π•_ {s = s} s′ s″)
  FM-isicms-•-assoc = {! !}

  FM-isicms-↖↑-↑-assoc : ∀ {i} {j}
    (s : S* i) (s′ : {j : I} → P* s j → S* j)
    (s″ : {j : I} {k : I} (p : P* s k) → P* (s′ p) j → S* j)
    → {! !}
  FM-isicms-↖↑-↑-assoc = {! !}

  FM-isicms-↑-↗↑-assoc : ∀ {i} {j}
    (s : S* i) (s′ : {j : I} → P* s j → S* j)
    (s″ : {j : I} {k : I} (p : P* s k) → P* (s′ p) j → S* j)
    → {! !}
  FM-isicms-↑-↗↑-assoc = {! !}

  FM-isicms-↖↖-↖-assoc : ∀ {i} {j}
    (s : S* i) (s′ : {j : I} → P* s j → S* j)
    (s″ : {j : I} {k : I} (p : P* s k) → P* (s′ p) j → S* j)
    → {! !}
  FM-isicms-↖↖-↖-assoc = {! !}

  FM-isicms-↖↗-↗↖-assoc : ∀ {i} {j}
    (s : S* i) (s′ : {j : I} → P* s j → S* j)
    (s″ : {j : I} {k : I} (p : P* s k) → P* (s′ p) j → S* j) 
    → {! !}
  FM-isicms-↖↗-↗↖-assoc = {! !}

  FM-isicms-↗-↗↗-assoc : ∀ {i} {j}
    (s : S* i) (s′ : {j : I} → P* s j → S* j)
    (s″ : {j : I} {k : I} (p : P* s k) → P* (s′ p) j → S* j) 
    → {! !}
  FM-isicms-↗-↗↗-assoc = {! !}

FM-isicms : isICMS′ FM-ricms
FM-isicms .e-unit-l = FM-isicms-e-unit-l
FM-isicms .↖-unit-l = FM-isicms-↖-unit-l
FM-isicms .e-unit-r s = substRefl {B = S*} s
FM-isicms .↗-unit-r = FM-isicms-↗-unit-r
FM-isicms .•-assoc = FM-isicms-•-assoc
FM-isicms .↑-↗↑-assoc = FM-isicms-↑-↗↑-assoc 
FM-isicms .↖↑-↑-assoc = FM-isicms-↖↑-↑-assoc
FM-isicms .↖↖-↖-assoc = FM-isicms-↖↖-↖-assoc
FM-isicms .↖↗-↗↖-assoc = FM-isicms-↖↗-↗↖-assoc
FM-isicms .↗-↗↗-assoc = FM-isicms-↗-↗↗-assoc 
