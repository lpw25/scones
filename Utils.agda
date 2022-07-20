{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws

module Utils where

  transportComposite :
    ∀ {ℓ} {A B C : Type ℓ} (p : A ≡ B) (q : B ≡ C) (x : A) →
      transport (p ∙ q) x ≡ transport q (transport p x)
  transportComposite = substComposite (λ B -> B)

  isSet-subst-swap : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
                  → (isSet-A : isSet A)
                  → ∀ {a b : A}
                  → (p q : a ≡ b) → (x : B a) → subst B p x ≡ subst B q x
  isSet-subst-swap {B = B} isSet-A p q x =
    subst (λ p' → subst B p x ≡ subst B p' x) (isSet-A _ _ p q) refl

  substSubst⁻ :
    ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (B : A → Type ℓ') (p : x ≡ y) (b : B y) →
      subst B p (subst⁻ B p b) ≡ b
  substSubst⁻ B p = transportTransport⁻ (cong B p)

  subst⁻Subst :
    ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (B : A → Type ℓ') (p : x ≡ y) (b : B x) →
      subst⁻ B p (subst B p b) ≡ b
  subst⁻Subst B p = transport⁻Transport (cong B p)

  transportPathP :
    ∀ {ℓ} {A : I → Type ℓ} {A0 : Type ℓ} {p : A0 ≡ A i0} {x : A0} {y : A i1} →
      PathP (λ i → (p ∙ λ i → A i) i) x y → PathP A (transport p x) y
  transportPathP {ℓ} {A} {A0} {p} {x} {y} q =
    toPathP (sym (transportComposite p (λ i → A i) x) ∙ fromPathP q)

  substPathP :
    ∀ {ℓ ℓ'} {A : Type ℓ} (B : A -> Type ℓ') {a b c : A} (p : a ≡ b) {x : B a} {q : b ≡ c} {y : B c} →
      PathP (λ i → cong B (p ∙ q) i) x y → PathP (λ i -> cong B q i) (subst B p x) y
  substPathP B p {x = x} {q = q} r = toPathP (sym (substComposite B p q x) ∙ fromPathP r)

  substPathP⁻ :
    ∀ {ℓ ℓ'} {A : Type ℓ} (B : A -> Type ℓ') {a b c : A} (p : b ≡ a) {x : B a} {q : b ≡ c} {y : B c} →
      PathP (λ i → cong B (sym p ∙ q) i) x y → PathP (λ i -> cong B q i) (subst⁻ B p x) y
  substPathP⁻ B p r = substPathP B (sym p) r

  slicePathP :
    ∀ {ℓ ℓ'} {A : Type ℓ} (B C : A -> Type ℓ')
      (F : (u : A) → B u → C u) {a1 a2 : A} {b1 : B a1} {b2 : B a2} (p : a1 ≡ a2) →
        PathP (λ i → cong B p i) b1 b2 →
          PathP (λ i -> cong C p i) (F a1 b1) (F a2 b2)
  slicePathP B C F {a2 = a2} {b1 = b1} p q =
    toPathP (substCommSlice B C F p b1 ∙ cong (F a2) (fromPathP q))

  isSetPathP :
    ∀ {ℓ ℓ'} {A : Type ℓ} (isSet-A : isSet A) (B : A -> Type ℓ')
      {a b : A} (p : a ≡ b) {q : a ≡ b} {x : B a} {y : B b} →
        PathP (λ i -> cong B p i) x y -> PathP (λ i -> cong B q i) x y
  isSetPathP {ℓ} {ℓ'} {A} isSet-A B {a} {b} p {q} {x} {y} r =
    transport (λ j -> PathP (λ i -> cong B (isSet-A a b p q j) i) x y) r

  symPathP :
    ∀ {ℓ ℓ'} {A : Type ℓ} (B : A -> Type ℓ') {a b : A} {p : a ≡ b} {x : B a} {y : B b} ->
      PathP (λ i -> cong B (sym p) i) y x -> PathP (λ i -> cong B p i) x y
  symPathP B q = symP q

  rcancelPathP :
    ∀ {ℓ ℓ'} {A : Type ℓ} (B : A -> Type ℓ') {a b : A} {p : a ≡ b} {x y : B a} (q : x ≡ y) →
        PathP (λ i -> cong B (p ∙ sym p) i) x y
  rcancelPathP {ℓ} {ℓ'} {A} B {a} {b} {p} {x} {y} q =
    transport (λ i -> PathP (λ j -> B (rCancel p (~ i) j)) x y) q

  ΣPathP :
    ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} (B : A -> Type ℓ') (C : (a : A) -> B a -> Type ℓ'') {a b : A}
      {p : a ≡ b} {x : B a} {y : B b} {u : C a x} {v : C b y}
      (q : PathP (λ i -> cong B p i) x y) ->
      PathP (λ i -> C (p i) (q i)) u v ->
      PathP (λ i -> cong (λ x -> Σ (B x) (λ y -> C x y)) p i) (x , u) (y , v)
  ΣPathP B C {p = p} q r =
    λ i -> q i , r i
