open import Prelude

open import Cubical.Data.Nat
open import IndexedContainer ℕ

module IndexedMonad.Examples.ScopedLambda where

open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr)
open IndexedContainer

data LamS (n : ℕ) : Type where
  var :                       LamS n
  app : (M N : LamS n)      → LamS n
  lam : (M : LamS (suc n))  → LamS n

module _ {ℓ} {B : ℕ → Type ℓ}  
  (var* : {n : ℕ} → B n) 
  (app* : {n : ℕ} → B n → B n → B n) 
  (lam* : {n : ℕ} → B (suc n) → B n) where

  LamS-rec : ∀ {n} (s : LamS n) → B n
  LamS-rec var = var*
  LamS-rec (app M N) = app* (LamS-rec M) (LamS-rec N)
  LamS-rec (lam M) = lam* (LamS-rec M)

module _ {ℓ} {B : ∀ {n} → LamS n → Type ℓ}  
  (var* : {n : ℕ} → B {n} var) 
  (app* : {n : ℕ} {M N : LamS n} → B M → B N → B (app M N)) 
  (lam* : {n : ℕ} {M : LamS (suc n)} → B M → B (lam M)) where

  LamS-elim : ∀ {n} (s : LamS n) → B s
  LamS-elim var = var*
  LamS-elim (app M N) = app* (LamS-elim M) (LamS-elim N)
  LamS-elim (lam M) = lam* (LamS-elim M)

LamP : ∀ {n} → LamS n → ℕ → Type 
LamP {n} var m = n ≡ m
LamP (app M N) m = LamP M m ⊎ LamP N m
LamP {n} (lam M) m = LamP {suc n} M m

Lam : IndexedContainer
Lam .S = LamS
Lam .P = LamP

-- Claim: Well scoped lambda terms are ⟦ Lam ⟧ Fin 0
open import Cubical.Data.Fin using (Fin)

[_,_] = Sum.rec 
subst′ : {A : Type} (B : A → Type) {x y : A} → B x → x ≡ y → B y
subst′ B bx p = subst B p bx

infix 30 #_
#_ : {x y : ℕ} → Fin x → x ≡ y → Fin y
#_ = subst′ Fin

λ1⟨00⟩ : ⟦ Lam ⟧ Fin 1
λ1⟨00⟩ .fst = lam (app var (app var var))
λ1⟨00⟩ .snd = [ # 1 , [ # 0 , # 0 ] ]

Y-comb : ⟦ Lam ⟧ Fin 0
Y-comb .fst = lam (app (λ1⟨00⟩ .fst) (λ1⟨00⟩ .fst))
Y-comb .snd = [ λ1⟨00⟩ .snd , λ1⟨00⟩ .snd ]

Y-comb² : ⟦ Lam ⟧ (⟦ Lam ⟧ Fin) 0
Y-comb² .fst = lam (app var var)
Y-comb² .snd = [ subst′ (⟦ Lam ⟧ Fin) λ1⟨00⟩ , subst′ (⟦ Lam ⟧ Fin) λ1⟨00⟩ ]

open import IndexedMonad ℕ Lam

private
  lam-ricms-• : ∀ {i} (s : LamS i) → ({j : ℕ} → LamP s j → LamS j) → LamS i
  lam-ricms-• var       σ = σ refl
  lam-ricms-• (app M N) σ = app (lam-ricms-• M (inl » σ)) (lam-ricms-• N (inr » σ))
  lam-ricms-• (lam M)   σ = lam (lam-ricms-• M σ)
  
  lam-ricms-↑ : ∀ {i} (s : LamS i) (s′ : {j : ℕ} → LamP s j → LamS j) {j : ℕ} (p : LamP (lam-ricms-• s s′) j) → ℕ
  lam-ricms-↑ {i} var _ _ = i
  lam-ricms-↑ (app M N) σ (inl p) = lam-ricms-↑ M (inl » σ) p
  lam-ricms-↑ (app M N) σ (inr p) = lam-ricms-↑ N (inr » σ) p 
  lam-ricms-↑ (lam M) σ p = lam-ricms-↑ M σ p

  lam-ricms-↖ : ∀ {i} (s : LamS i) (s′ : {j : ℕ} → LamP s j → LamS j) {j : ℕ} (p : LamP (lam-ricms-• s s′) j) → LamP s (lam-ricms-↑ s s′ p)
  lam-ricms-↖ var σ p = refl
  lam-ricms-↖ (app M N) σ (inl p) = inl (lam-ricms-↖ M (inl » σ) p)
  lam-ricms-↖ (app M N) σ (inr p) = inr (lam-ricms-↖ N (inr » σ) p)
  lam-ricms-↖ (lam M) σ p = lam-ricms-↖ M σ p

  lam-ricms-↗ : ∀ {i} (s : LamS i) (s′ : {j : ℕ} → LamP s j → LamS j) {j : ℕ} (p : LamP (lam-ricms-• s s′) j) → LamP (s′ (lam-ricms-↖ s s′ p)) j
  lam-ricms-↗ var σ p = p
  lam-ricms-↗ (app M N) σ (inl p) = lam-ricms-↗ M (inl » σ) p
  lam-ricms-↗ (app M N) σ (inr p) = lam-ricms-↗ N (inr » σ) p
  lam-ricms-↗ (lam M) σ p = lam-ricms-↗ M σ p

module _ where
  open RawICMS
  lam-ricms : RawICMS
  lam-ricms .e n = var
  lam-ricms ._•_ {i} = lam-ricms-• {i}
  lam-ricms ._↑_ {s} = lam-ricms-↑ s 
  lam-ricms ._↖_ {s} = lam-ricms-↖ s
  lam-ricms ._↗_ {s} = lam-ricms-↗ s
  lam-ricms .P-e-idx = idfun _

open isICMS
open import Cubical.Data.Nat using (isSetℕ)

private
  open RawICMS lam-ricms
  lam-isicms-e-unit-l : ∀ {i} (s : LamS i) → lam-ricms-• s (λ {j} _ → var) ≡ s
  lam-isicms-e-unit-l var = refl
  lam-isicms-e-unit-l (app M N) = cong₂ app (lam-isicms-e-unit-l M) (lam-isicms-e-unit-l N)
  lam-isicms-e-unit-l (lam M) = cong lam (lam-isicms-e-unit-l M)

lam-isicms : isICMS lam-ricms
lam-isicms .e-unit-l = lam-isicms-e-unit-l
lam-isicms .↖-unit-l var {j} = funExt λ _ → isSetℕ _ _ _ _ 
lam-isicms .↖-unit-l (app M N) {j} = {! !} -- similarly to below but the type of P does not compute to ⊎
lam-isicms .↖-unit-l {i} (lam M) {j} = funExtConstCod (congP (λ ι → lam-isicms .↖-unit-l M {j} ι))
lam-isicms .e-unit-r s = substRefl {B = LamS} s
lam-isicms .↗-unit-r {i} s {j} ι p = transp (λ κ → LamP {n = i} (substRefl {B = LamS} s (ι ∨ κ)) j) ι p
lam-isicms .•-assoc var s′ s″ = refl
lam-isicms .•-assoc (app M N) s′ s″ = cong₂ app
  (lam-isicms .•-assoc M (inl » s′) (inl » s″))
  (lam-isicms .•-assoc N (inr » s′) (inr » s″))
lam-isicms .•-assoc (lam M) s′ s″ = cong lam (lam-isicms .•-assoc M s′ s″)
lam-isicms .↑-↗↑-assoc {i} var s′ s″  = funExt λ _ → refl 
lam-isicms .↑-↗↑-assoc (app M N) s′ s″ = {! !}
lam-isicms .↑-↗↑-assoc (lam M) s′ s″ = {! !}
lam-isicms .↖↑-↑-assoc = {! !}
lam-isicms .↖↖-↖-assoc = {! !}
lam-isicms .↖↗-↗↖-assoc = {! !}
lam-isicms .↗-↗↗-assoc = {! !}
