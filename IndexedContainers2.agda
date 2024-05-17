open import Cubical.Foundations.Prelude hiding (_∙_)
open import Cubical.Core.Primitives using (Level; ℓ-zero; ℓ-suc)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep)

open import Prelude

module IndexedContainers2 (indices : Type) where

record IndexedContainer  : Type (ℓ-suc ℓ-zero) where
  field
    S : (i : indices) → Type
    P : {i : indices} → S i → (j : indices) → Type

open IndexedContainer

record _⇒_ (F G : IndexedContainer) : Type ℓ-zero where
  field
    smap : ∀ i → F .S i → G .S i
    pmap : ∀ {i} (s : F .S i) {j} → G .P (smap i s) j → F .P s j

open _⇒_

idᶜ : IndexedContainer
idᶜ .S _ = Unit
idᶜ .P _ _ = Unit

module _ (F : IndexedContainer) where
  ⟦_⟧ : (indices → Type) → (indices → Type)
  ⟦_⟧ X i = Σ[ s ∈ F .S i ] (∀ j (p : F .P s j) → X j)

  _⟨$⟩_ : {X Y : indices → Type} → (∀ i → X i → Y i) → (∀ i → ⟦ X ⟧ i → ⟦ Y ⟧ i)
  _⟨$⟩_ f i (s , v) .fst = s
  _⟨$⟩_ f i (s , v) .snd j p = f j (v j p)

module _ (F G : IndexedContainer) where
  _;_ : IndexedContainer
  _;_ .S = ⟦ G ⟧ (F .S) 
  _;_ .P (s′ , v) i = Σ[ j ∈ indices ] Σ[ p′ ∈ G .P s′ j ] F .P (v j p′) i

  module _ (X : indices → Type) (i : indices) where
    ;-≃ : ∀ i → ⟦ G ⟧ (⟦ F ⟧ X) i ≃ ⟦ _;_ ⟧ X i
    ;-≃ i = isoToEquiv ;-iso where
      open Iso
      ;-iso : Iso (⟦ G ⟧ (⟦ F ⟧ X) i) (⟦ _;_ ⟧ X i)
      ;-iso .fun (s′ , br) = (s′ , λ j p → br j p .fst) , λ { k (j , (p′ , p)) → br j p′ .snd k p }
      ;-iso .inv ((s′ , br) , ;ops) = s′ , λ { j p′ → br j p′ , λ { k p → ;ops k (j , p′ , p) } }
      ;-iso .rightInv _ = refl
      ;-iso .leftInv _ = refl

module _ {F} where
  unitor-l : (idᶜ ; F) ⇒ F
  unitor-l .smap _ (s , _) = s
  unitor-l .pmap (s , _) p = _ , p , _

  unitor-r : (F ; idᶜ) ⇒ F
  unitor-r .smap _ (_ , ubr) = ubr _ _
  unitor-r .pmap _ p = _ , _ , p

module _ {F G H} where
  associator : (F ; (G ; H)) ⇒ ((F ; G) ; H)
  associator .smap _ ((s″ , op″) , op′) = s″ , λ j p″ → op″ j p″ , λ i p′ → op′ i (j , p″ , p′)
  associator .pmap ((s″ , op″) , op′) (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p

module _ {F G} {α β : F ⇒ G} where
  ⇒PathP :
    (≡smap : (α .smap) ≡ (β .smap))
    (≡pmap : (λ {i} → α .pmap {i}) ≡[ ≡smap ,  (λ sm → ∀ {i} s {j} → G .P (sm i s) j → F .P s j) ] (λ {i} → β .pmap {i}))
    → α ≡ β
  ⇒PathP ≡smap ≡pmap i = record { smap = ≡smap i ; pmap = ≡pmap i }

_² : IndexedContainer → IndexedContainer
IC ² = IC ; IC

module _ {F} where
  id₁ : F ⇒ F 
  id₁ .smap _ s = s
  id₁ .pmap s p = p

module _ {F G H K} where
  _;ₕ_ : (α : F ⇒ H) (β : G ⇒ K) → (F ; G) ⇒ (H ; K)
  (α ;ₕ β) .smap _ (s′ , br) = β .smap _ s′ , λ { j p′ → α .smap _ (br j (β .pmap s′ p′)) }
  (α ;ₕ β) .pmap = λ { (s′ , br) (j , (t′ , br′)) → j , β .pmap s′ t′ , α .pmap (br j (β .pmap s′ t′)) br′ } 

module _ {F G H} where
  _;ᵥ_ : (α : F ⇒ G) (β : G ⇒ H) → (F ⇒ H)
  (α ;ᵥ β) .smap _ s = β .smap _ (α .smap _ s)
  (α ;ᵥ β) .pmap s p = α .pmap s (β .pmap (α .smap _ s) p)

module _ (T : IndexedContainer) where 
  record ICMonoid : Type ℓ-zero where
    field
      η : idᶜ ⇒ T
      μ : (T ²) ⇒ T
      η-unit-l : (η ;ₕ id₁) ;ᵥ μ ≡ unitor-l
      η-unit-r : (id₁ {F = T} ;ₕ η) ;ᵥ μ ≡ unitor-r
      μ-assoc : (id₁ {F = T} ;ₕ μ) ;ᵥ μ ≡ (associator {F = T} ;ᵥ ((μ ;ₕ id₁) ;ᵥ μ))

  open ICMonoid

  record ICMS : Type ℓ-zero where
    field
      e  : ∀ i → T .S i
      _∙_ : ∀ {i} (s : T .S i)
        → (∀ j (p : T .P s j) → T .S j)
        → T .S i
      _↖ᵢ_ : ∀ {i} {s : T .S i}
        → (v : ∀ j (p : T .P s j) → T .S j)
        → {j : indices}
        → T .P (s ∙ v) j
        → indices
      _↖_ : ∀ {i} {s : T .S i}
        → (v : ∀ j (p : T .P s j) → T .S j)
        → {j : indices}
        → (p : T .P (s ∙ v) j)
        → T .P s (v ↖ᵢ p)
      _↗_ : ∀ {i} {s : T .S i}
        → (v : ∀ j (p : T .P s j) → T .S j)
        → {j : indices}
        → (p : T .P (s ∙ v) j)
        → T .P (v (v ↖ᵢ p) (v ↖ p)) j
--       e-unit-l : ∀ i (s : S i) → s ≡ (e i) ∙ λ p → {! subst S (pi-e i p) !} s
      e-unit-r : ∀ i (s : T .S i) → s ∙ (λ j _ → e j) ≡ s 
--
--       ∙-assoc : ∀ i 
--         (s : S i)
--         (v : (p : P s) → S (pi p))
--         (w :  (p : P s) → (p′ : P (v p)) → S (pi p′))
--         → ((s ∙ v) ∙ λ p → subst S (pi-∙ i s v p) (w (v ↖ p) (v ↗ p))) ≡ s ∙ (λ p → v p ∙ w p)
-- 
-- 
  module _ (icms : ICMS) where
    open ICMS icms

    ICMS→ICMonoid : ICMonoid
    ICMS→ICMonoid .η .smap i = λ _ → e i
    ICMS→ICMonoid .η .pmap = λ _ _ → tt
    ICMS→ICMonoid .μ .smap _ (s , br) = s ∙ br
    ICMS→ICMonoid .μ .pmap (s , br) p = br ↖ᵢ p , br ↖ p , (br ↗ p)
    ICMS→ICMonoid .η-unit-l = ⇒PathP
      (funExt₂ λ { i (s , _) → e-unit-r i s })
      -- (implicitFunExt λ {i} → 
      --   funExtDep λ { {x₀ = (s₀ , br₀)}{x₁ = (s₁ , br₁)} ≡smap → implicitFunExt λ {j} → funExtDep λ p → {! !} })
      {! !}
    ICMS→ICMonoid .η-unit-r = {! !}
    ICMS→ICMonoid .μ-assoc = {! !}

  -- λ s p → ((λ j p′ → e j) ↖ᵢ p) ≡ id
  -- λ j p′ → e j) ↖ p ≡ id
