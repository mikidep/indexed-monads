open import Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function using (idfun; curry; uncurry; _∘_)
open import Cubical.Foundations.Equiv

open import Cubical.Reflection.StrictEquiv

import IndexedContainer as ICModule

module IndexedMonad (I : Type) (T : ICModule.IndexedContainer I) where

open ICModule I
open import IndexedContainer.MonoidalCategory {I}

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

ICMonoid : Type
ICMonoid = Σ RawICMonoid isICMonoid

record RawICMS : Type where
  infixl 24 _•_
  field
    e  : ∀ i → S i
    _•_ : ∀ {i} (s : S i)
      → (s′ : ∀ {j} (p : P s j) → S j)
      → S i
    _↑_ : ∀ {i} {s : S i}
      → (s′ : ∀ {j} (p : P s j) → S j)
      → {j : I} (p : P (s • s′) j)
      → I 
    _↖_ : ∀ {i} {s : S i}
      → (s′ : ∀ {j} (p : P s j) → S j)
      → {j : I} (p : P (s • s′) j)
      → P s (s′ ↑ p)
    _↗_ : ∀ {i} {s : S i}
      → (s′ : ∀ {j} (p : P s j) → S j)
      → {j : I} (p : P (s • s′) j)
      → P (s′ (s′ ↖ p)) j
    P-e-idx : ∀ {i} {j} → P (e i) j → i ≡ j

  infixl 24 _Π•_

  const-e : ∀ {i : I} {s : S i} {j : I} (p : P s j) → S j
  const-e {j} _ = e j

  substS-Pe : ∀ {i : I} (s : S i) {k : I} → P (e i) k → S k
  substS-Pe s p = subst S (P-e-idx p) s

  _Π•_ : ∀ {i} {s : S i}
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → ∀ {j} (p : P s j) → S j
  (s′ Π• s″) {j} p = s′ p • s″ p

  smoosh : ∀ {i} {s : S i}
      {s′ : {j : I} → P s j → S j}
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → ∀ {j} (p : P (s • s′) j) → S j
  smoosh {s′} s″ p = s″ (s′ ↖ p) (s′ ↗ p)

  curry″ : ∀ {i} {s : S i}
      {s′ : {j : I} → P s j → S j}
      (s″ : {j : I} → Σ I (λ k → Σ (P s k) (λ p → P (s′ p) j)) → S j)
      → {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j
  curry″ s″ p q = s″ (_ , p , q)

  uncurry″ : ∀ {i} {s : S i}
      {s′ : {j : I} → P s j → S j}
      → ({j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → {j : I} → Σ I (λ k → Σ (P s k) (λ p → P (s′ p) j)) → S j
  uncurry″ s″ (_ , p , q) = s″ p q

record isICMS (raw : RawICMS) : Type where
  open RawICMS raw
  field
    e-unit-l : ∀ {i} (s : S i)
      → s • const-e ≡ s 

    ↖-unit-l : ∀ {i} (s : S i) {j}
      → PathP (λ z → P (e-unit-l s z) j → P s j)
        (λ (p : P (s • const-e) j) →
           (subst (P s) (P-e-idx (_ ↗ p)))
           (_ ↖ p)
        )
        (λ p → p)

    e-unit-r : ∀ {i} (s : S i)
      → e i • (λ p → subst S (P-e-idx p) s) ≡ s

    ↗-unit-r : ∀ {i} (s : S i) {j}
      → PathP (λ ι → P (e-unit-r s ι) j → P s j)
        (λ p →
          let eq = P-e-idx (_ ↖ p) 
          in transport
            (cong₂ (λ i s → P {i} s j) (sym eq) (symP $ subst-filler S eq s))
            (_ ↗ p)
        )
        (λ p → p)

    •-assoc : ∀ {i} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → s • s′ • smoosh s″ ≡ s • (s′ Π• s″)

    -- new
    ↑-↗↑-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → I) 
        (_ ↑_)
        (_ ↗_ » _ ↑_) 

    -- new
    ↖↑-↑-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → I) 
          (_ ↖_ » _ ↑_)
          (_ ↑_)

    ↖↖-↖-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P s (↖↑-↑-assoc s s′ s″ ι p)) 
        (_ ↖_ » _ ↖_)
        (_ ↖_)

    ↖↗-↗↖-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P (s′ (↖↖-↖-assoc s s′ s″ ι p)) (↑-↗↑-assoc s s′ s″ ι p)) 
        (_ ↖_ » _ ↗_) 
        (_ ↗_ » _ ↖_)

    ↗-↗↗-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P (s″ (↖↖-↖-assoc s s′ s″ ι p) (↖↗-↗↖-assoc s s′ s″ ι p)) j)
        (_ ↗_)
        (_ ↗_ » _ ↗_)

record isICMS′ (raw : RawICMS) : Type where
  open RawICMS raw
  field
    e-unit-l : ∀ {i} (s : S i)
      → s • const-e ≡ s 

    ↖-unit-l : ∀ {i} (s : S i) {j : I} (p : P (s • const-e) j)
      → PathP (λ ι → P (e-unit-l s (~ ι)) (P-e-idx (const-e ↗ p) ι))
         (const-e ↖ p) p

    e-unit-r : ∀ {i} (s : S i)
      → e i • (substS-Pe s) ≡ s

    ↗-unit-r : ∀ {i} (s : S i) {j}
      → (p : P (e i • substS-Pe s) j)
      → PathP (λ ι →
          let
            eq : i ≡ substS-Pe s ↑ p
            eq = P-e-idx (substS-Pe s ↖ p)
          in P (transp (λ κ → S (eq (ι ∧ κ))) (~ ι) (e-unit-r s ι)) j)
        p
        (substS-Pe s ↗ p)

    •-assoc : ∀ {i} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → s • s′ • smoosh s″ ≡ s • (s′ Π• s″)

    -- new
    ↑-↗↑-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → I) 
        (λ p → smoosh s″ ↑ p)
        (λ p → s″ (s′ Π• s″ ↖ p) ↑ (s′ Π• s″ ↗ p)) 

    -- new
    ↖↑-↑-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → I) 
          (λ p → s′ ↑ (smoosh s″ ↖ p))
          (λ p → s′ Π• s″ ↑ p)

    ↖↖-↖-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P s (↖↑-↑-assoc s s′ s″ ι p)) 
        (λ p → s′ ↖ (smoosh s″ ↖ p))
        (λ p → s′ Π• s″ ↖ p)

    ↖↗-↗↖-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P (s′ (↖↖-↖-assoc s s′ s″ ι p)) (↑-↗↑-assoc s s′ s″ ι p)) 
        (λ p → s′ ↗ (smoosh s″ ↖ p))
        (λ p → s″ (s′ Π• s″ ↖ p) ↖ (s′ Π• s″ ↗ p)) 

    ↗-↗↗-assoc : ∀ {i} {j} 
      (s : S i)
      (s′ : {j : I} → P s j → S j)
      (s″ : {j : I} → ∀ {k} (p : P s k) → P (s′ p) j → S j)
      → PathP (λ ι → (p : P (•-assoc s s′ s″ ι) j) → P (s″ (↖↖-↖-assoc s s′ s″ ι p) (↖↗-↗↖-assoc s s′ s″ ι p)) j)
        (λ p → smoosh s″ ↗ p)
        (λ p → s″ (s′ Π• s″ ↖ p) ↗ (s′ Π• s″ ↗ p))

ICMS : Type
ICMS = Σ RawICMS isICMS

module _ (icms : RawICMS) where
  open RawICMS icms
  open RawICMonoid

  RawICMS→RawICMonoid : RawICMonoid
  RawICMS→RawICMonoid .η i _ .fst = e i
  RawICMS→RawICMonoid .η _ _ .snd p = P-e-idx p
  RawICMS→RawICMonoid .μ _ (s , s′) .fst = s • s′
  RawICMS→RawICMonoid .μ _ (_ , s′) .snd p = s′ ↑ p , s′ ↖ p , s′ ↗ p

  open isICMonoid

  module _ (is-icms : isICMS icms) where
    open isICMS is-icms
    open import Cubical.Functions.FunExtEquiv using (funExt₂)

    isICMS→isICMonoid : isICMonoid RawICMS→RawICMonoid
    isICMS→isICMonoid .η-unit-l = funExt₂ λ i s → ΣPathP (e-unit-l s , implicitFunExt λ {j} → ↖-unit-l s)
    isICMS→isICMonoid .η-unit-r = funExt₂ λ i s → ΣPathP (e-unit-r s , implicitFunExt λ {j} → ↗-unit-r s)
    isICMS→isICMonoid .μ-assoc = funExt₂ λ { i ((s , s′) , s″) → ΣPathP 
        (•-assoc s s′ (curry″ s″) , implicitFunExt λ {j} →
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
    RawICMonoid→RawICMS .e i = η i _ .fst
    RawICMonoid→RawICMS .P-e-idx {i} p = η i _ .snd p
    RawICMonoid→RawICMS ._•_ {i} s s′ = μ i (s , s′) .fst
    RawICMonoid→RawICMS ._↑_ {i} {s} s′ p = μ i (s , s′) .snd p .fst
    RawICMonoid→RawICMS ._↖_ {i} {s} s′ p = μ i (s , s′) .snd p .snd .fst
    RawICMonoid→RawICMS ._↗_ {i} {s} s′ p = μ i (s , s′) .snd p .snd .snd

  module _ (is-icmon : isICMonoid icmon) where
    open RawICMS RawICMonoid→RawICMS

    open isICMS
    open isICMonoid is-icmon

    isICMonoid→isICMS : isICMS RawICMonoid→RawICMS
    isICMonoid→isICMS .e-unit-l = σs≡ η-unit-l 
    isICMonoid→isICMS .↖-unit-l = πs≡ η-unit-l
    isICMonoid→isICMS .e-unit-r = σs≡ η-unit-r
    isICMonoid→isICMS .↗-unit-r = πs≡ η-unit-r
    isICMonoid→isICMS .•-assoc     s s′ s″ = σs≡ μ-assoc ((s , s′) , uncurry″ s″)
    isICMonoid→isICMS .↑-↗↑-assoc  s s′ s″ ι p = πs≡ μ-assoc ((s , s′) , uncurry″ s″) ι p .fst
    isICMonoid→isICMS .↖↑-↑-assoc  s s′ s″ ι p = πs≡ μ-assoc ((s , s′) , uncurry″ s″) ι p .snd .fst .fst
    isICMonoid→isICMS .↖↖-↖-assoc  s s′ s″ ι p = πs≡ μ-assoc ((s , s′) , uncurry″ s″) ι p .snd .fst .snd .fst
    isICMonoid→isICMS .↖↗-↗↖-assoc s s′ s″ ι p = πs≡ μ-assoc ((s , s′) , uncurry″ s″) ι p .snd .fst .snd .snd
    isICMonoid→isICMS .↗-↗↗-assoc  s s′ s″ ι p = πs≡ μ-assoc ((s , s′) , uncurry″ s″) ι p .snd .snd

ICMonoid→ICMS : ICMonoid → ICMS
ICMonoid→ICMS (raw , is) = RawICMonoid→RawICMS raw , isICMonoid→isICMS raw is

ICMS→ICMonoid : ICMS → ICMonoid
ICMS→ICMonoid (raw , is) = RawICMS→RawICMonoid raw , isICMS→isICMonoid raw is

unquoteDecl ICMonoid≃ICMS = declStrictEquiv ICMonoid≃ICMS ICMonoid→ICMS ICMS→ICMonoid

