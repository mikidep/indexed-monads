open import Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function using (idfun; curry; uncurry; _∘_)

import IndexedContainer as ICModule

module IndexedMonads (I : Type) (T : ICModule.IndexedContainer I) where

open ICModule I

open IndexedContainer T

record RawICMonoid : Type where
  field
    η : idᶜ ⇒ T
    μ : (T ²) ⇒ T

record isICMonoid (raw : RawICMonoid) : Type where
  open RawICMonoid raw
  field
    η-unit-l : unitor-l-inv ; (η ⊗₁ id₁ T) ; μ ≡ id₁ T
    η-unit-r : unitor-r-inv ; (id₁ T ⊗₁ η) ; μ ≡ id₁ T
    μ-assoc : (id₁ T ⊗₁ μ) ; μ ≡ (associator {F = T} ; ((μ ⊗₁ id₁ T) ; μ))

record RawICMS : Type where
  infixl 24 _•_
  field
    e  : ∀ i → S i
    _•_ : ∀ {i} (s : S i)
      → (v : ∀ {j} (p : P s j) → S j)
      → S i
    _↑_ : ∀ {i} {s : S i}
      → (v : ∀ {j} (p : P s j) → S j)
      → {j : I} (p : P (s • v) j)
      → I 
    _↖_ : ∀ {i} {s : S i}
      → (v : ∀ {j} (p : P s j) → S j)
      → {j : I} (p : P (s • v) j)
      → P s (v ↑ p)
    _↗_ : ∀ {i} {s : S i}
      → (v : ∀ {j} (p : P s j) → S j)
      → {j : I} (p : P (s • v) j)
      → P (v (v ↖ p)) j
    P-e-idx : ∀ {i} {j} → P (e i) j → i ≡ j

  infixl 24 _Π•_

  const-e : ∀ {i : I} {s : S i} {j : I} (p : P s j) → S j
  const-e {j} _ = e j

  substS-Pe : ∀ {i : I} (s : S i) {k : I} → P (e i) k → S k
  substS-Pe s p = subst S (P-e-idx p) s

  _Π•_ : ∀ {i} {s : S i}
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
      → ∀ {j} (p : P s j) → S j
  (s′ Π• s″) {j} p = s′ p • s″ j p

  smoosh : ∀ {i} {s : S i}
      {s′ : {j : I} → P s j → S j}
      (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
      → ∀ {j} (p : P (s • s′) j) → S j
  smoosh {s′} s″ p = s″ (s′ ↑ p) (s′ ↖ p) (s′ ↗ p)

  curry″ : ∀ {i} {s : S i}
      {s′ : {j : I} → P s j → S j}
      (s″ : {j : I} → Σ I (λ k → Σ (P s k) (λ p → P (s′ p) j)) → S j)
      → {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j
  curry″ s″ k p q = s″ (k , p , q)

  uncurry″ : ∀ {i} {s : S i}
      {s′ : {j : I} → P s j → S j}
      → ({j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
      → {j : I} → Σ I (λ k → Σ (P s k) (λ p → P (s′ p) j)) → S j
  uncurry″ s″ (k , p , q) = s″ k p q

record isICMS (raw : RawICMS) : Type where
  open RawICMS raw
  field
    e-unit-l : ∀ {i} (s : S i)
      → s • const-e ≡ s 

    ↖-unit-l : ∀ {i} (s : S i) {j}
      → PathP (λ z → P (e-unit-l s z) j → P s j)
        (λ (p : P (s • const-e) j) →
           (subst (P s) (P-e-idx (const-e ↗ p)))
           (const-e ↖ p)
        )
        (λ p → p)

    e-unit-r : ∀ {i} (s : S i)
      → e i • (λ p → subst S (P-e-idx p) s) ≡ s

    ↗-unit-r : ∀ {i} (s : S i) {j}
      → PathP (λ ι → P (e-unit-r s ι) j → P s j)
        (λ p →
          let eq = P-e-idx (substS-Pe s ↖ p) 
          in transport
            (cong₂ (λ i s → P {i} s j) (sym eq) (symP $ subst-filler S eq s))
            (substS-Pe s ↗ p)
        )
        (λ p → p)

    •-assoc : ∀ {i} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
      → s • s′ • smoosh s″ ≡ s • (s′ Π• s″)

    -- new
    ↑-↗↑-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → I) 
        (λ p → smoosh s″ ↑ p)
        (λ p → s″ ((s′ Π• s″) ↑ p) ((s′ Π• s″) ↖ p) ↑ (s′ Π• s″ ↗ p)) 

    -- new
    ↖↑-↑-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → I) 
          (λ p → s′ ↑ (smoosh s″ ↖ p))
          (λ p → (s′ Π• s″) ↑ p)

    ↖↖-↖-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P s (↖↑-↑-assoc s s′ s″ ι p)) 
        (λ p → s′ ↖ (smoosh s″ ↖ p))
        (λ p → s′ Π• s″ ↖ p)

    ↖↗-↗↖-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P (s′ (↖↖-↖-assoc s s′ s″ ι p)) (↑-↗↑-assoc s s′ s″ ι p)) 
        (λ p → s′ ↗ (smoosh s″ ↖ p))
        (λ p → s″ (s′ Π• s″ ↑ p) (s′ Π• s″ ↖ p) ↖ (s′ Π• s″ ↗ p)) 

    ↗-↗↗-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ k (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P (s″ (↖↑-↑-assoc s s′ s″ ι p) (↖↖-↖-assoc s s′ s″ ι p) (↖↗-↗↖-assoc s s′ s″ ι p)) j)
        (λ p → smoosh s″ ↗ p)
        (λ p → s″ ((s′ Π• s″) ↑ p) ((s′ Π• s″) ↖ p) ↗ ((s′ Π• s″) ↗ p))

record ICMS : Type where
  field
    icms : RawICMS
    is-icms : isICMS icms

module _ (icms : RawICMS) where
  open RawICMS icms
  open RawICMonoid

  RawICMS→RawICMonoid : RawICMonoid
  RawICMS→RawICMonoid .η i _ .σs = e i
  RawICMS→RawICMonoid .η _ _ .πs p = P-e-idx p
  RawICMS→RawICMonoid .μ _ (s , v) .σs = s • v
  RawICMS→RawICMonoid .μ _ (_ , v) .πs p = v ↑ p , v ↖ p , v ↗ p

  open isICMonoid

  module _ (is-icms : isICMS icms) where
    open isICMS is-icms

    isICMS→isICMonoid : isICMonoid RawICMS→RawICMonoid
    isICMS→isICMonoid .η-unit-l = ⇒PathP λ s → Π⇒PathP
      (e-unit-l s)
      (implicitFunExt λ {j} → ↖-unit-l s)
    isICMS→isICMonoid .η-unit-r = ⇒PathP λ {i} s → Π⇒PathP
      (e-unit-r s)
      (implicitFunExt λ {j} → ↗-unit-r s)
    isICMS→isICMonoid .μ-assoc = ⇒PathP λ { ((s , s′) , s″) → Π⇒PathP
        (•-assoc s s′ (curry″ s″))
        (implicitFunExt λ {j} →
          λ { ι p →
              ↑-↗↑-assoc s s′ (curry″ s″) ι p 
            , ( ↖↑-↑-assoc s s′ (curry″ s″) ι p 
              , ↖↖-↖-assoc s s′ (curry″ s″) ι p 
              , ↖↗-↗↖-assoc s s′ (curry″ s″) ι p
              ) 
            , ↗-↗↗-assoc s s′ (curry″ s″) ι p
          }
        )
      }

module _ (icmon : RawICMonoid) where
  open RawICMonoid icmon

  module _ where
    open RawICMS

    RawICMonoid→RawICMS : RawICMS
    RawICMonoid→RawICMS .e i = η i _ .σs
    RawICMonoid→RawICMS .P-e-idx {i} p = η i _ .πs p
    RawICMonoid→RawICMS ._•_ {i} s v = μ i (s , v) .σs
    RawICMonoid→RawICMS ._↑_ {i} {s} v p = μ i (s , v) .πs p .fst
    RawICMonoid→RawICMS ._↖_ {i} {s} v p = μ i (s , v) .πs p .snd .fst
    RawICMonoid→RawICMS ._↗_ {i} {s} v p = μ i (s , v) .πs p .snd .snd

  module _ (is-icmon : isICMonoid icmon) where
    open RawICMS RawICMonoid→RawICMS
    
    open isICMS
    open isICMonoid is-icmon

    isICMonoid→isICMS : isICMS RawICMonoid→RawICMS
    isICMonoid→isICMS .e-unit-l = σs≡ η-unit-l 
    isICMonoid→isICMS .↖-unit-l = πs≡ η-unit-l
    isICMonoid→isICMS .e-unit-r = σs≡ η-unit-r
    isICMonoid→isICMS .↗-unit-r = πs≡ η-unit-r
    isICMonoid→isICMS .•-assoc s s′ s″ = σs≡ μ-assoc ((s , s′) , uncurry″ s″)
    isICMonoid→isICMS .↑-↗↑-assoc {j} s s′ s″ ι p = πs≡ μ-assoc ((s , s′) , uncurry″ s″) {j} ι p .fst
    isICMonoid→isICMS .↖↑-↑-assoc {j} s s′ s″ ι p = πs≡ μ-assoc ((s , s′) , uncurry″ s″) {j} ι p .snd .fst .fst
    isICMonoid→isICMS .↖↖-↖-assoc {j} s s′ s″ ι p = πs≡ μ-assoc ((s , s′) , uncurry″ s″) {j} ι p .snd .fst .snd .fst
    isICMonoid→isICMS .↖↗-↗↖-assoc {j} s s′ s″ ι p = πs≡ μ-assoc ((s , s′) , uncurry″ s″) {j} ι p .snd .fst .snd .snd
    isICMonoid→isICMS .↗-↗↗-assoc {j} s s′ s″ ι p = πs≡ μ-assoc ((s , s′) , uncurry″ s″) {j} ι p .snd .snd

module _ (icms : RawICMS) where
  inv-RawICMS : (icms € RawICMS→RawICMonoid € RawICMonoid→RawICMS) ≡ icms
  inv-RawICMS = refl

  module _ (is-icms : isICMS icms) where
    inv-isICMS : (is-icms € isICMS→isICMonoid icms € isICMonoid→isICMS _) ≡ is-icms
    inv-isICMS = refl

module _ (icmon : RawICMonoid) where
  inv-RawICMonoid : (icmon € RawICMonoid→RawICMS € RawICMS→RawICMonoid) ≡ icmon
  inv-RawICMonoid = refl

  module _ (is-icmon : isICMonoid icmon) where
    inv-isICMonoid : (is-icmon € isICMonoid→isICMS icmon € isICMS→isICMonoid _) ≡ is-icmon
    inv-isICMonoid = refl

