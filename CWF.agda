{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

-- Positivity check broken with path composition in indices
-- see https://github.com/agda/agda/issues/5625
{-# NO_POSITIVITY_CHECK #-}
data Context : Set

variable
  Γ : Context
  Δ : Context
  Θ : Context

data _⟶_ : Context -> Context -> Set

variable
  σ : Γ ⟶ Δ
  δ : Γ ⟶ Δ
  θ : Γ ⟶ Δ

data Typ : Context -> Set

variable
  A : Typ Γ

data Elem : (Γ : Context) -> Typ Γ -> Set

variable
  a : Elem Γ A

data Context where
  [] : Context
  _+_ : (Γ : Context) -> Typ Γ -> Context

infix 30 _+_

subst-compose : Δ ⟶ Θ -> Γ ⟶ Δ -> Γ ⟶ Θ
subst-p : Γ + A ⟶ Γ
type-action : Typ Γ -> Δ ⟶ Γ -> Typ Δ
type-action-associativity' : type-action (type-action A σ) δ ≡ type-action A (subst-compose σ δ)
elem-action : {Δ Γ : Context} {A : Typ Γ} -> Elem Γ A -> (σ : Δ ⟶ Γ) -> Elem Δ (type-action A σ)
elem-q : Elem (Γ + A) (type-action A subst-p)

data _⟶_ where
  id : Γ ⟶ Γ
  _∘_ : Δ ⟶ Θ -> Γ ⟶ Δ -> Γ ⟶ Θ
  left-identity : id ∘ σ ≡ σ
  right-identity : σ ∘ id ≡ σ
  associativity : (σ ∘ δ) ∘ θ ≡ σ ∘ (δ ∘ θ)
  ε : Γ ⟶ []
  ε-unique : σ ≡ ε
  p : Γ + A ⟶ Γ
  _+_ : {Δ Γ : Context} {A : Typ Γ} (σ : Δ ⟶ Γ) -> Elem Δ (type-action A σ) -> Δ ⟶ Γ + A
  weakening : p ∘ (σ + a) ≡ σ
  subst-+ :
    PathP (λ i -> Θ ⟶ (Γ + A)) (σ + a ∘ δ)
          ((subst-compose σ δ) + transport (λ i -> Elem Θ (type-action-associativity' {A = A} {σ = σ} {δ = δ} i))
          (elem-action a δ))
  p-q-identity : _+_ {A = A} subst-p elem-q ≡ id

subst-compose = _∘_
subst-p = p

data Typ where
  _∘_ : Typ Γ -> Δ ⟶ Γ -> Typ Δ
  type-action-identity : A ∘ id ≡ A
  type-action-associativity : (A ∘ σ) ∘ δ ≡ A ∘ (σ ∘ δ)

type-action = _∘_
type-action-associativity' = type-action-associativity

data Elem where
  _∘_ : {Δ Γ : Context} {A : Typ Γ} -> Elem Γ A -> (σ : Δ ⟶ Γ) -> Elem Δ (A ∘ σ)
  elem-action-identity :
    PathP (λ i -> Elem Γ (type-action-identity {Γ} {A} i)) (a ∘ id) a
  elem-action-associativity :
    PathP (λ i -> Elem Γ (type-action-associativity {Θ} {A} {Δ} {σ} {Γ} {δ} i)) ((a ∘ σ) ∘ δ) (a ∘ (σ ∘ δ))
  q : Elem (Γ + A) (A ∘ p)
  var : PathP (λ i -> Elem Δ ((type-action-associativity ∙ λ i -> A ∘ (weakening {a = a} i)) i))
              (q ∘ (σ + a)) a

elem-action = _∘_
elem-q = q

∣_∣ : Context -> Set
∣ Γ ∣ = [] ⟶ Γ

