open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives using (Level; ℓ-zero; ℓ-suc)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep)
open import Cubical.Foundations.Function using (idfun)

open import Prelude

module IndexedContainers2 (I : Type) where

record IndexedContainer  : Type (ℓ-suc ℓ-zero) where
  field
    S : (i : I) → Type
    P : {i : I} → S i → (j : I) → Type

open IndexedContainer

record _⇒_ (F G : IndexedContainer) : Type ℓ-zero where
  field
    smap : ∀ i → F .S i → G .S i
    pmap : ∀ {i} (s : F .S i) j → G .P (smap i s) j → F .P s j

open _⇒_

module _ {F G} {α β : F ⇒ G} where
  ⇒PathP :
    (≡smap : α .smap ≡ β .smap)
    (≡pmap : PathP (λ 𝒾 → ∀ {i} (s : F .S i) j → G .P (≡smap 𝒾 i s) j → F .P s j) (α .pmap) (β .pmap))
    → α ≡ β
  ⇒PathP ≡smap ≡pmap 𝒾 .smap = ≡smap 𝒾
  ⇒PathP ≡smap ≡pmap 𝒾 .pmap = ≡pmap 𝒾

  ⇒PathP-ext :
    (≡smap : ∀ {i} s → α .smap i s ≡ β .smap i s)
    (≡pmap : ∀ (i : I) s j
      → {p₁ : G .P (α .smap i s) j} {p₂ : G .P (β .smap i s) j}
        (p≡ : p₁ ≡[ ≡smap s , (λ s′ → G .P s′ j) ] p₂)
      → (α .pmap s j p₁) ≡ (β .pmap s j p₂))
    → α ≡ β
  ⇒PathP-ext ≡smap ≡pmap = ⇒PathP
    (funExt₂ λ _ s → ≡smap s)
    (implicitFunExt λ {i} → funExt₂ λ s j → funExtDep (≡pmap i s j))

idᶜ : IndexedContainer
idᶜ .S _ = Unit
idᶜ .P _ _ = Unit

module _ (F : IndexedContainer) where
  ⟦_⟧ : (I → Type) → (I → Type)
  ⟦_⟧ X i = Σ[ s ∈ F .S i ] (∀ j (p : F .P s j) → X j)

  _⟨$⟩_ : {X Y : I → Type} → (∀ i → X i → Y i) → (∀ i → ⟦ X ⟧ i → ⟦ Y ⟧ i)
  _⟨$⟩_ f i (s , v) .fst = s
  _⟨$⟩_ f i (s , v) .snd j p = f j (v j p)

module _ (F G : IndexedContainer) where
  _;_ : IndexedContainer
  _;_ .S = ⟦ G ⟧ (F .S) 
  _;_ .P (s′ , v) i = Σ[ j ∈ I ] Σ[ p′ ∈ G .P s′ j ] F .P (v j p′) i
  
  -- interpretation is strong monoidal
  module _ (X : I → Type) (i : I) where
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
      _•_ : ∀ {i} (s : T .S i)
        → (∀ j (p : T .P s j) → T .S j)
        → T .S i
      _↖_ : ∀ {i} {s : T .S i}
        → (v : ∀ j (p : T .P s j) → T .S j)
        → {j : I}
        → (p : T .P (s • v) j)
        → Σ I (T .P s) 
      _↗_ : ∀ {i} {s : T .S i}
        → (v : ∀ j (p : T .P s j) → T .S j)
        → {j : I}
        → (p : T .P (s • v) j)
        → T .P (v ((v ↖ p) .fst) ((v ↖ p) .snd)) j
      e-unit-l : ∀ i (sect-s : ∀ j → T .S j) → (e i • (λ j _ → sect-s j)) ≡ sect-s i 
      e-unit-r : ∀ i (s : T .S i) → s • (λ j _ → e j) ≡ s 
      e-act-l₁ : ∀ i (sect-s : ∀ i′ → T .S i′) j (p : T .P (sect-s i) j)
        → ((λ j _ → sect-s j) ↖ subst (λ s → T .P s j) (sym (e-unit-l i sect-s)) p) .fst ≡ i
      e-act-l₂ : ∀ i (sect-s : ∀ i′ → T .S i′) j (p : T .P (sect-s i) j)
        → (λ j _ → sect-s j) ↗ subst (λ s → T .P s j) (sym (e-unit-l i sect-s)) p ≡ subst (λ i → T .P (sect-s i) j) {! !} p
      e-act-r : ∀ i (s : T .S i) j (p : T .P s j)
        → (λ j _ → e j) ↖ subst (λ s → T .P s j) (sym (e-unit-r i s)) p ≡ (j , p)
--
--       •-assoc : ∀ i 
--         (s : S i)
--         (v : (p : P s) → S (pi p))
--         (w :  (p : P s) → (p′ : P (v p)) → S (pi p′))
--         → ((s • v) • λ p → subst S (pi-• i s v p) (w (v ↖ p) (v ↗ p))) ≡ s • (λ p → v p • w p) 
-- 
-- 
  module _ (icms : ICMS) where
    open ICMS icms
    open ICMonoid

    ICMS→ICMonoid : ICMonoid
    ICMS→ICMonoid .η .smap i _ = e i
    ICMS→ICMonoid .η .pmap = _
    ICMS→ICMonoid .μ .smap i (s , TPs→ᵢTS)= s • TPs→ᵢTS
    ICMS→ICMonoid .μ .pmap (s , TPs→ᵢTS) j TPs• = let
        (i′ , p′) = TPs→ᵢTS ↖ TPs•
        p″ = TPs→ᵢTS ↗ TPs• 
      in i′ , p′ , p″
    ICMS→ICMonoid .η-unit-l = ⇒PathP-ext
      (λ { (s , _) → e-unit-r _ s })
      λ { i (s , _) j {p₁} {p₂} p≡ → 
        let
          eq = e-act-r i s j p₂
        in {! !} }
    ICMS→ICMonoid .η-unit-r = ⇒PathP-ext
      (λ { {i} (_ , sect-s) → e-unit-l i λ { j → sect-s j tt } })
      λ { i (_ , sect-s) j {p₁} p≡ → {! ((λ j₁ Ksp → sect-s j₁ tt) ↖ p₁)!} }
    ICMS→ICMonoid .μ-assoc = {! !}

  module _ (icmon : ICMonoid) where
    open ICMS
    open ICMonoid icmon

    ICMonoid→ICMS : ICMS
    ICMonoid→ICMS .e i = η .smap i _
    ICMonoid→ICMS ._•_ {i} s TPs→ᵢTS = μ .smap i (s , TPs→ᵢTS)
    ICMonoid→ICMS ._↖_ {i} {s} TPs→ᵢTS {j} TPs• = 
        let i′ , p′ , _ = μ .pmap (s , TPs→ᵢTS) j TPs•
      in i′ , p′
    ICMonoid→ICMS ._↗_ {i} {s} TPs→ᵢTS {j} TPs• = 
        let _ , _ , p″ = μ .pmap (s , TPs→ᵢTS) j TPs•
      in p″
    ICMonoid→ICMS .e-unit-l = {! !}
    ICMonoid→ICMS .e-unit-r = {! !}
    ICMonoid→ICMS .e-act-l₁ = {! !}
    ICMonoid→ICMS .e-act-r = {! !}
    
