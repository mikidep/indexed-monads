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

open isICMS
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

  FM-isicms-↖-unit-l : ∀ {i} (s : S* i) {j : I} →
    PathP (λ z → P* (FM-isicms-e-unit-l s z) j → P* s j)
    (λ p →
       transp (λ i₁ → P* s (FM-ricms-↗ s (λ _ → η) p i₁)) i0
       (FM-ricms-↖ s (λ _ → η) p))
    (λ p → p)
  FM-isicms-↖-unit-l {i} η ι p = transp (λ κ → i ≡ p (ι ∨ κ)) ι (λ κ → p (ι ∧ κ))
  FM-isicms-↖-unit-l {i} (sup (s , ps*)) {j} ι p = {! !}

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

FM-isicms : isICMS FM-ricms
FM-isicms .e-unit-l = FM-isicms-e-unit-l
FM-isicms .↖-unit-l = FM-isicms-↖-unit-l
FM-isicms .e-unit-r s = substRefl {B = S*} s
FM-isicms .↗-unit-r {i} s {j} ι p = transp (λ κ → P* {i} (substRefl {B = S*} s (ι ∨ κ)) j) ι p
FM-isicms .•-assoc = FM-isicms-•-assoc
FM-isicms .↑-↗↑-assoc = FM-isicms-↑-↗↑-assoc 
FM-isicms .↖↑-↑-assoc = FM-isicms-↖↑-↑-assoc
FM-isicms .↖↖-↖-assoc = FM-isicms-↖↖-↖-assoc
FM-isicms .↖↗-↗↖-assoc = FM-isicms-↖↗-↗↖-assoc
FM-isicms .↗-↗↗-assoc = FM-isicms-↗-↗↗-assoc 
