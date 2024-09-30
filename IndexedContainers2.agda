open import Cubical.Foundations.Prelude hiding (_∙_)
open import Cubical.Core.Primitives using (Level; ℓ-zero; ℓ-suc)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep)
open import Cubical.Foundations.Function using (idfun)

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
    pmap : ∀ {i} (s : F .S i) j → G .P (smap i s) j → F .P s j

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
  
  -- interpretation is strong monoidal
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
  unitor-l .pmap (s , _) j p = j , p , _

  unitor-r : (F ; idᶜ) ⇒ F
  unitor-r .smap i (_ , ubr) = ubr i tt
  unitor-r .pmap {i} (_ , s) j p = i , _ , p

module _ {F G H} where
  associator : (F ; (G ; H)) ⇒ ((F ; G) ; H)
  associator .smap _ ((s″ , op″) , op′) = s″ , λ j p″ → op″ j p″ , λ i p′ → op′ i (j , p″ , p′)
  associator .pmap ((s″ , op″) , op′) j′  (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p

module _ {F G} {α β : F ⇒ G} where
  ⇒PathP :
    (≡smap : (α .smap) ≡ (β .smap))
    (≡pmap : (λ {i} → α .pmap {i}) ≡[ ≡smap ,  (λ sm → ∀ {i} s j → G .P (sm i s) j → F .P s j) ] (λ {i} → β .pmap {i}))
    → α ≡ β
  ⇒PathP ≡smap ≡pmap i = record { smap = ≡smap i ; pmap = ≡pmap i }

_² : IndexedContainer → IndexedContainer
IC ² = IC ; IC

module _ {F} where
  id₁ : F ⇒ F 
  id₁ .smap _ s = s
  id₁ .pmap s j p = p

module _ {F G H K} where
  _;ₕ_ : (α : F ⇒ H) (β : G ⇒ K) → (F ; G) ⇒ (H ; K)
  (α ;ₕ β) .smap _ (Gs , Gsp→Fs) = β .smap _ Gs , λ { j Ksp → α .smap j (Gsp→Fs j (β .pmap Gs j Ksp)) }
  (α ;ₕ β) .pmap {i} (Gs , Gsp→Fs) j (i′ , Kp , Hp) = let
      Gsp = β .pmap Gs i′ Kp 
    in i′ , Gsp , α .pmap (Gsp→Fs i′ Gsp) j Hp

module _ {F G H} where
  _;ᵥ_ : (α : F ⇒ G) (β : G ⇒ H) → (F ⇒ H)
  (α ;ᵥ β) .smap _ s = β .smap _ (α .smap _ s)
  (α ;ᵥ β) .pmap s _ p = α .pmap s _ (β .pmap (α .smap _ s) _ p)

module _ {F G} where
  id₁-;ₕ : id₁ {F} ;ₕ id₁ {G} ≡ id₁ {F ; G}
  id₁-;ₕ = ⇒PathP
    (λ i j p → p)
    λ i {k} s j p → p

module _ (T : IndexedContainer) where 
  record ICMonoid : Type ℓ-zero where
    field
      η : idᶜ ⇒ T
      μ : (T ²) ⇒ T
      η-unit-l : (η ;ₕ id₁) ;ᵥ μ ≡ unitor-l
      η-unit-r : (id₁ {F = T} ;ₕ η) ;ᵥ μ ≡ unitor-r
      μ-assoc : (id₁ {F = T} ;ₕ μ) ;ᵥ μ ≡ (associator {F = T} ;ᵥ ((μ ;ₕ id₁) ;ᵥ μ))

  record ICMS : Type ℓ-zero where
    field
      e  : ∀ i → T .S i
      _∙_ : ∀ {i} (s : T .S i)
        → (∀ j (p : T .P s j) → T .S j)
        → T .S i
      _↖ᵢ_ : ∀ {i} {s : T .S i}
        → (v : ∀ j (p : T .P s j) → T .S j)
        → {j : indices}
        → (p : T .P (s ∙ v) j)
        → indices
      _↖_ : ∀ {i} {s : T .S i}
        → (v : ∀ j (p : T .P s j) → T .S j)
        → {j : indices}
        → (p : T .P (s ∙ v) j)
        → T .P s (v ↖ᵢ p)
      _↗ᵢ_ : ∀ {i} {s : T .S i}
        → (v : ∀ j (p : T .P s j) → T .S j)
        → {j : indices}
        → (p : T .P (s ∙ v) j)
        → indices
      _↗_ : ∀ {i} {s : T .S i}
        → (v : ∀ j (p : T .P s j) → T .S j)
        → {j : indices}
        → (p : T .P (s ∙ v) j)
        → T .P (v (v ↖ᵢ p) (v ↖ p)) (v ↗ᵢ p)
      e-unit-l : ∀ i (s : ∀ j → T .S j) → (e i ∙ (λ j _ → s j)) ≡ s i 
      e-unit-r : ∀ i (s : T .S i) → s ∙ (λ j _ → e j) ≡ s 
      -- e-act-l : ∀ {i} (s : T .S i) {j} → (λ p → (λ j _ → e j) ↖ p) ≡[ e-unit-r i s , (λ s′ → T .P s′ j → T .P s j) ] idfun _ 
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
    open ICMonoid

    -- ICMS→ICMonoid : ICMonoid
    -- ICMS→ICMonoid .η .smap i = λ _ → e i
    -- ICMS→ICMonoid .η .pmap = λ _ _ _ → tt
    -- ICMS→ICMonoid .μ .smap _ (s , br) = s ∙ br
    -- ICMS→ICMonoid .μ .pmap (s , br) _ p = _ , br ↖ p , (br ↗ p)
    -- ICMS→ICMonoid .η-unit-l = ⇒PathP
    --   (funExt₂ λ { i (s , _) → e-unit-r i s })
    --   {! !} -- λ { i (s , _) j p → j , e-act-l s i p , tt }
    -- ICMS→ICMonoid .η-unit-r = ⇒PathP
    --   (funExt₂ λ { i (_ , s) → e-unit-l i λ j → s j tt })
    --   λ { i (_ , s) j p → {! !} }
    -- ICMS→ICMonoid .μ-assoc = {! !}

    --   (implicitFunExt λ {i} → funExt λ { (s , _) → λ i → λ j p → j , e-act-l s i p , tt })
    --
    --
    --   Start figuring out inverse data

  module _ (icmon : ICMonoid) where
    open ICMS
    open ICMonoid icmon

    ICMonoid→ICMS : ICMS
    ICMonoid→ICMS = {! !}
    
