open import Cubical.Foundations.Prelude hiding (_∙_)
open import Cubical.Core.Primitives using (Level; ℓ-zero; ℓ-suc)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)

module IndexedContainers2 (indices : Type) where

record IndexedContainer  : Type (ℓ-suc ℓ-zero) where
  field
    shapes : (i : indices) → Type
    positions : {i : indices} → shapes i → (j : indices) → Type

open IndexedContainer

record _⇒_ (F G : IndexedContainer) : Type ℓ-zero where
  field
    smap : ∀ {i} → F .shapes i → G .shapes i
    pmap : ∀ {i} (s : F .shapes i) {j} → G .positions (smap s) j → F .positions s j

open _⇒_

id⇒ : ∀ {F} → F ⇒ F
id⇒ .smap s = s
id⇒ .pmap s p = p

idᶜ : IndexedContainer
idᶜ .shapes _ = Unit
idᶜ .positions _ _ = Unit

module _ (F : IndexedContainer) where
  private
    S = F .shapes
    P = F .positions

  ⟦_⟧ : (indices → Type) → (indices → Type)
  ⟦_⟧ X i = Σ[ s ∈ S i ] (∀ j (p : P s j) → X j)

  _⟨$⟩_ : {X Y : indices → Type} → (∀ i → X i → Y i) → (∀ i → ⟦ X ⟧ i → ⟦ Y ⟧ i)
  _⟨$⟩_ f i (s , v) .fst = s
  _⟨$⟩_ f i (s , v) .snd j p = f j (v j p)

module _ (F G : IndexedContainer) where
  private
    S = F .shapes
    P = F .positions
    S′ = G .shapes
    P′ = G .positions

  _;_ : IndexedContainer
  _;_ .shapes = ⟦ G ⟧ S 
  _;_ .positions (s′ , v) i = Σ[ j ∈ indices ] Σ[ p′ ∈ P′ s′ j ] P (v j p′) i

  module _ (X : indices → Type) (i : indices) where
    ;-≃ : ∀ i → ⟦ G ⟧ (⟦ F ⟧ X) i ≃ ⟦ _;_ ⟧ X i
    ;-≃ i = isoToEquiv ;-iso where
      open Iso
      ;-iso : Iso (⟦ G ⟧ (⟦ F ⟧ X) i) (⟦ _;_ ⟧ X i)
      ;-iso .fun (s′ , br) = (s′ , λ j p → br j p .fst) , λ { k (j , (p′ , p)) → br j p′ .snd k p }
      ;-iso .inv ((s′ , br) , ;ops) = s′ , λ { j p′ → br j p′ , λ { k p → ;ops k (j , p′ , p) } }
      ;-iso .rightInv _ = refl
      ;-iso .leftInv _ = refl

_² : IndexedContainer → IndexedContainer
IC ² = IC ; IC

module _ {F G H K}   where
  _;ₕ_ : (α : F ⇒ H) (β : G ⇒ K) → (F ; G) ⇒ (H ; K)
  (α ;ₕ β) .smap (s′ , br) = β .smap s′ , λ { j p′ → α .smap (br j (β .pmap s′ p′)) }
  (α ;ₕ β) .pmap = let
      αsmap = α .smap
      βsmap = β .smap
      αpmap = α .pmap
      βpmap = β .pmap
    in λ { (s′ , br) (j , (t′ , br′)) → j , β .pmap s′ t′ , α .pmap (br j (β .pmap s′ t′)) br′ } 
-- 
-- module _ 
--     (S : indices → Type)
--     (P : {i : indices} → S i → Type)
--     (pi : {i : indices} {s : S i} → P s → indices) where
-- 
--   T : IndexedContainer
--   T .shapes = S
--   T .positions = P
--   T .positionIndex = pi
-- 
--   record ICMonad : Type ℓ-zero where
--     field
--       η : idᶜ ⇒ T
--       μ : (T ²) ⇒ T
-- 
--   open ICMonad
-- 
--   record ICMS : Type ℓ-zero where
--     field
--       e  : ∀ i → S i
--       _∙_ : ∀ {i} (s : S i)
--         → ((p : P s) → S (pi p))
--         → S i
--       _↖_ : ∀ {i} {s : S i}
--         → (v : (p : P s) → S (pi p))
--         → P (s ∙ v)
--         → P s
--       _↗_ : ∀ {i} {s : S i}
--         → (v : (p : P s) → S (pi p))
--         → (p′ : P (s ∙ v))
--         → P (v (v ↖ p′))
-- 
--       pi-e : ∀ i (p : P (e i)) → i ≡ pi p
--       pi-∙ : ∀ i s (v : (p : P s) → S (pi p)) (p : P (s ∙ v)) → pi (v ↗ p) ≡ pi p
--       e-unit-l : ∀ i (s : S i) → s ≡ (e i) ∙ λ p → {! subst S (pi-e i p) !} s
--       e-unit-r : ∀ i (s : S i) → s ≡ s ∙ λ p → e (pi p) 
--       ∙-assoc : ∀ i 
--         (s : S i)
--         (v : (p : P s) → S (pi p))
--         (w :  (p : P s) → (p′ : P (v p)) → S (pi p′))
--         → ((s ∙ v) ∙ λ p → subst S (pi-∙ i s v p) (w (v ↖ p) (v ↗ p))) ≡ s ∙ (λ p → v p ∙ w p)
-- 
-- 
--   module _ (icms : ICMS) where
--     open ICMS icms
-- 
--     ICMS→ICMonad : ICMonad
--     ICMS→ICMonad .η .smap = λ i _ → e i
--     ICMS→ICMonad .η .pmap = λ _ _ _ → tt
--     ICMS→ICMonad .η .pimap = λ i s p′ → pi-e i p′
--     ICMS→ICMonad .μ .smap = λ { i (s , v) → s ∙ v }
--     ICMS→ICMonad .μ .pmap = λ { i (s , v) p → (v ↖ p) , (v ↗ p) }
--     ICMS→ICMonad .μ .pimap = λ { i (s , v) p′ → pi-∙ i s v p′ }
