{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Utils

module STLC where

  record Model (l : Level) : Set (lsuc l) where
    field
      Context : Set l
      _↣_ : Context -> Context -> Set l
      Typ : Set l
      Elem : (Γ : Context) -> Typ -> Set l
      subst-is-set : {Γ Δ : Context} -> isSet (Γ ↣ Δ)
      elem-is-set : {Γ : Context} -> {A : Typ} -> isSet (Elem Γ A)
      [] : Context
      _⊹_ : (Γ : Context) -> Typ -> Context
      id : {Γ : Context} -> Γ ↣ Γ
      _∘_ : {Γ Δ Θ : Context} -> Δ ↣ Θ -> Γ ↣ Δ -> Γ ↣ Θ
      left-identity : {Γ Δ : Context} (σ : Γ ↣ Δ) -> id ∘ σ ≡ σ
      right-identity : {Γ Δ : Context} (σ : Γ ↣ Δ) -> σ ∘ id ≡ σ
      associativity :
        {Γ Δ Θ Ψ : Context} (σ : Θ ↣ Ψ) (δ : Δ ↣ Θ) (θ : Γ ↣ Δ) ->
        (σ ∘ δ) ∘ θ ≡ σ ∘ (δ ∘ θ)
      ε : {Γ : Context} -> Γ ↣ []
      ε-unique : {Γ : Context} (σ : Γ ↣ []) -> σ ≡ ε
      p : {Γ : Context} (A : Typ) -> (Γ ⊹ A) ↣ Γ
      _+_ : {Δ Γ : Context} {A : Typ} (σ : Δ ↣ Γ) -> Elem Δ A -> Δ ↣ (Γ ⊹ A)
      weakening :
        {Γ Δ : Context} {A : Typ} (σ : Γ ↣ Δ) (a : Elem Γ A) ->
        p A ∘ (σ + a) ≡ σ
      arrow : Typ -> Typ -> Typ
      bool : Typ
      _[_] : {Δ Γ : Context} {A : Typ} -> Elem Γ A -> (σ : Δ ↣ Γ) -> Elem Δ A
      subst-+ :
        {Γ Δ Θ : Context} {A : Typ} (σ : Γ ↣ Δ) (δ : Θ ↣ Γ) (a : Elem Γ A) ->
        (σ + a) ∘ δ ≡ (σ ∘ δ) + (a [ δ ])
      elem-action-identity : {Γ : Context} {A : Typ} (a : Elem Γ A) -> a [ id ] ≡ a
      elem-action-associativity :
        {Γ Δ Θ : Context} {A : Typ} (σ : Γ ↣ Δ) (δ : Θ ↣ Γ) (a : Elem Δ A) ->
        (a [ σ ]) [ δ ] ≡ a [ σ ∘ δ ]
      q : {Γ : Context} {A : Typ} -> Elem (Γ ⊹ A) A
      var : {Γ Δ : Context} {A : Typ} (σ : Γ ↣ Δ) (a : Elem Γ A) -> q [ σ + a ] ≡ a
      p-q-identity : {Γ : Context} {A : Typ} -> (p {Γ} A) + q ≡ id
      abs : {Γ : Context} {A B : Typ} -> Elem (Γ ⊹ A) B -> Elem Γ (arrow A B)
      app : {Γ : Context} {A B : Typ} -> Elem Γ (arrow A B) -> Elem Γ A -> Elem Γ B
      subst-abs :
        {Γ Δ : Context} {A B : Typ} (σ : Γ ↣ Δ) (a : Elem (Δ ⊹ A) B) ->
        (abs a) [ σ ] ≡ abs (a [ (σ ∘ p A) + q ])
      subst-app :
        {Γ Δ : Context} {A B : Typ} (σ : Γ ↣ Δ) (a : Elem Δ (arrow A B)) (b : Elem Δ A) ->
        (app a b) [ σ ] ≡ app (a [ σ ]) (b [ σ ])
      arrow-beta :
        {Γ : Context} {A B : Typ} (a : Elem (Γ ⊹ A) B) (b : Elem Γ A) ->
        app (abs a) b ≡ a [ id + b ]
      arrow-eta :
        {Γ : Context} {A B : Typ} (a : Elem Γ (arrow A B)) ->
        a ≡ abs (app (a [ p A ]) q)
      true : {Γ : Context} -> Elem Γ bool
      false : {Γ : Context} -> Elem Γ bool
      brec : {Γ : Context} -> (A : Typ) -> Elem Γ A -> Elem Γ A -> Elem Γ (arrow bool A)
      subst-true : {Γ Δ : Context} (σ : Γ ↣ Δ) ->
        true [ σ ] ≡ true
      subst-false : {Γ Δ : Context} (σ : Γ ↣ Δ) ->
        false [ σ ] ≡ false
      subst-brec :
        {Γ Δ : Context} {A : Typ} (σ : Γ ↣ Δ) (a : Elem Δ A) (b : Elem Δ A) ->
        brec A a b [ σ ] ≡ brec A (a [ σ ]) (b [ σ ])
      bool-beta-true :
        {Γ : Context} {A : Typ} (a : Elem Γ A) (b : Elem Γ A) ->
        app (brec A a b) true ≡ a
      bool-beta-false :
        {Γ : Context} {A : Typ} (a : Elem Γ A) (b : Elem Γ A) ->
        app (brec A a b) false ≡ b
    ∣_∣ : Context -> Set l
    ∣ Γ ∣ = [] ↣ Γ
    ⟨_⟩ : {Γ : Context} {A : Typ} -> Elem Γ A -> Γ ↣ (Γ ⊹ A)
    ⟨ a ⟩ = id + a

  record Model-Morphism {l₁ l₂} (M : Model l₁) (N : Model l₂) : Set (l₁ ⊔ l₂)  where
    open Model
    field
      C : Context M -> Context N
      S : {Γ Δ : Context M} -> _↣_ M Γ Δ -> _↣_ N (C Γ) (C Δ)
      T : Typ M -> Typ N
      E : {Γ : Context M} {A : Typ M} -> Elem M Γ A -> Elem N (C Γ) (T A)
      preserve-[] : C ([] M) ≡ [] N
      preserve-extend :
        (Γ : Context M) (A : Typ M) -> C (_⊹_ M Γ A) ≡ _⊹_ N (C Γ) (T A)
      preserve-id : {Γ : Context M} -> S (id M {Γ}) ≡ id N {C Γ}
      preserve-compose :
        {Γ Δ Θ : Context M} (σ : _↣_ M Δ Θ) (δ : _↣_ M Γ Δ) ->
          S (_∘_ M σ δ) ≡ _∘_ N (S σ) (S δ)
      preserve-ε : {Γ : Context M} ->
        S (ε M {Γ}) ≡ subst (λ Δ -> _↣_ N (C Γ) Δ) (sym preserve-[]) (ε N {C Γ})
      preserve-p : {Γ : Context M} {A : Typ M} ->
        S (p M {Γ} A) ≡ subst (λ Δ -> _↣_ N Δ (C Γ)) (sym (preserve-extend Γ A)) (p N {C Γ} (T A))
      preserve-subst-extend :
        {Δ Γ : Context M} {A : Typ M} (σ : _↣_ M Δ Γ) (a : Elem M Δ A) ->
          S (_+_ M σ a) ≡ subst (λ Θ -> _↣_ N (C Δ) Θ) (sym (preserve-extend Γ A)) (_+_ N (S σ) (E a))
      preserve-arrow : (A : Typ M) (B : Typ M) -> T (arrow M A B) ≡ arrow N (T A) (T B)
      preserve-bool : T (bool M) ≡ bool N
      preserve-subst-action :
        {Δ Γ : Context M} {A : Typ M} (a : Elem M Γ A) (σ : _↣_ M Δ Γ) ->
          E (_[_] M a σ) ≡ _[_] N (E a) (S σ)
      preserve-q : {Γ : Context M} {A : Typ M} ->
        E (q M {Γ} {A}) ≡ subst (λ Δ -> Elem N Δ (T A)) (sym (preserve-extend Γ A)) (q N {C Γ} {T A})
      preserve-abs :
        {Γ : Context M} {A B : Typ M} (a : Elem M (_⊹_ M Γ A) B) ->
          E (abs M a)
          ≡ subst (λ D -> Elem N (C Γ) D) (sym (preserve-arrow A B))
              (abs N (subst (λ Δ -> Elem N Δ (T B)) (preserve-extend Γ A) (E a)))
      preserve-app :
        {Γ : Context M} {A B : Typ M} (a : Elem M Γ (arrow M A B)) (b : Elem M Γ A) ->
          E (app M a b)
          ≡ app N (subst (Elem N (C Γ)) (preserve-arrow A B) (E a)) (E b)
      preserve-true : {Γ : Context M} ->
        E (true M {Γ}) ≡ subst (λ A -> Elem N (C Γ) A) (sym preserve-bool) (true N {C Γ})
      preserve-false : {Γ : Context M} ->
        E (false M {Γ}) ≡ subst (λ A -> Elem N (C Γ) A) (sym preserve-bool) (false N {C Γ})
      preserve-brec : {Γ : Context M} (A : Typ M) (a : Elem M Γ A) (b : Elem M Γ A) ->
        E (brec M {Γ} A a b)
        ≡ subst (λ B -> Elem N (C Γ) B) (sym (preserve-arrow (bool M) A))
            (subst (λ B -> Elem N (C Γ) (arrow N B (T A))) (sym preserve-bool)
              (brec N {C Γ} (T A) (E a) (E b)))

  module Initial where

    data Context : Set

    variable
      Γ : Context
      Δ : Context
      Θ : Context
      Ψ : Context

    data _↣_ : Context -> Context -> Set

    variable
      σ : Γ ↣ Δ
      δ : Γ ↣ Δ
      θ : Γ ↣ Δ

    data Typ : Set

    variable
      A : Typ
      B : Typ

    data Elem : (Γ : Context) -> Typ -> Set

    variable
      a : Elem Γ A
      b : Elem Γ A

    infix 30 _⊹_
    data Context where
      [] : Context
      _⊹_ : (Γ : Context) -> Typ -> Context

    ∣_∣ : Context -> Set
    ∣ Γ ∣ = [] ↣ Γ

    elem-action : {Δ Γ : Context} {A : Typ} -> Elem Γ A -> (σ : Δ ↣ Γ) -> Elem Δ A
    elem-q : Elem (Γ ⊹ A) A

    infix 30 _+_
    data _↣_ where
      id : Γ ↣ Γ
      _∘_ : Δ ↣ Θ -> Γ ↣ Δ -> Γ ↣ Θ
      left-identity : (σ : Γ ↣ Δ) -> id ∘ σ ≡ σ
      right-identity : (σ : Γ ↣ Δ) -> σ ∘ id ≡ σ
      associativity :
        (σ : Θ ↣ Ψ) (δ : Δ ↣ Θ) (θ : Γ ↣ Δ) ->
          (σ ∘ δ) ∘ θ ≡ σ ∘ (δ ∘ θ)
      ε : Γ ↣ []
      ε-unique : (σ : Γ ↣ []) -> σ ≡ ε
      p : (A : Typ) -> Γ ⊹ A ↣ Γ
      _+_ : {Δ Γ : Context} {A : Typ} (σ : Δ ↣ Γ) -> Elem Δ A -> Δ ↣ Γ ⊹ A
      weakening : (σ : Γ ↣ Δ) (a : Elem Γ A) -> p A ∘ (σ + a) ≡ σ
      subst-+ :
        (σ : Γ ↣ Δ) (δ : Θ ↣ Γ) (a : Elem Γ A) ->
          (σ + a ∘ δ) ≡((σ ∘ δ) + (elem-action a δ))
      p-q-identity : p {Γ} A + elem-q ≡ id
      is-set : (σ δ : Γ ↣ Δ) (p q : σ ≡ δ) -> p ≡ q

    ⟨_⟩ : Elem Γ A -> Γ ↣ Γ ⊹ A
    ⟨ a ⟩ = id + a

    data Typ where
      arrow : Typ -> Typ -> Typ
      bool : Typ

    data Elem where
      _[_] : {Δ Γ : Context} {A : Typ} -> Elem Γ A -> (σ : Δ ↣ Γ) -> Elem Δ A
      elem-action-identity : (a : Elem Γ A) -> a [ id ] ≡ a
      elem-action-associativity :
        (σ : Γ ↣ Δ) (δ : Θ ↣ Γ)(a : Elem Δ A) ->
          (a [ σ ]) [ δ ] ≡ a [ σ ∘ δ ]
      q : Elem (Γ ⊹ A) A
      var : (σ : Γ ↣ Δ) (a : Elem Γ A) -> q [ σ + a ] ≡ a
      abs : Elem (Γ ⊹ A) B -> Elem Γ (arrow A B)
      app : Elem Γ (arrow A B) -> Elem Γ A -> Elem Γ B
      subst-abs :
        (σ : Γ ↣ Δ) (a : Elem (Δ ⊹ A) B) ->
          (abs a) [ σ ] ≡ abs (a [ (σ ∘ p A) + q ])
      subst-app :
        (σ : Γ ↣ Δ) (a : Elem Δ (arrow A B)) (b : Elem Δ A) ->
          (app a b) [ σ ] ≡ app (a [ σ ]) (b [ σ ])
      arrow-beta :
        (a : Elem (Γ ⊹ A) B) (b : Elem Γ A) -> app (abs a) b ≡ a [ ⟨ b ⟩ ]
      arrow-eta :
        (a : Elem Γ (arrow A B)) -> a ≡ abs (app (a [ p A ]) q)
      true : Elem Γ bool
      false : Elem Γ bool
      brec : (A : Typ) -> Elem Γ A -> Elem Γ A -> Elem Γ (arrow bool A)
      subst-true : (σ : Γ ↣ Δ) -> true [ σ ] ≡ true
      subst-false : (σ : Γ ↣ Δ) -> false [ σ ] ≡ false
      subst-brec :
        (σ : Γ ↣ Δ) (a : Elem Δ A) (b : Elem Δ A) ->
          brec A a b [ σ ] ≡ brec A (a [ σ ]) (b [ σ ])
      bool-beta-true :
        (a b : Elem Γ A) -> app (brec A a b) true ≡ a
      bool-beta-false :
        (a b : Elem Γ A) -> app (brec A a b) false ≡ b
      is-set : (a b : Elem Γ A) (p q : a ≡ b) -> p ≡ q

    elem-action = _[_]
    elem-q = q

  initial-model : Model lzero
  initial-model =
    record {
      Context = Context;
      _↣_ = _↣_;
      Typ = Typ;
      Elem = Elem;
      subst-is-set = _↣_.is-set;
      elem-is-set = Elem.is-set;
      [] = [];
      _⊹_ = _⊹_;
      id = id;
      _∘_ = _∘_;
      left-identity = left-identity;
      right-identity = right-identity;
      associativity = associativity;
      ε = ε;
      ε-unique = ε-unique;
      p = p;
      _+_ = _+_;
      weakening = weakening;
      arrow = arrow;
      bool = bool;
      _[_] = _[_];
      subst-+ = subst-+;
      elem-action-identity = elem-action-identity;
      elem-action-associativity = elem-action-associativity;
      q = q;
      var = var;
      p-q-identity = p-q-identity;
      abs = abs;
      app = app;
      subst-abs = subst-abs;
      subst-app = subst-app;
      arrow-beta = arrow-beta;
      arrow-eta = arrow-eta;
      true = true;
      false = false;
      brec = brec;
      subst-true = subst-true;
      subst-false = subst-false;
      subst-brec = subst-brec;
      bool-beta-true = bool-beta-true;
      bool-beta-false = bool-beta-false
    }
    where open Initial

  initial-model-morphism :
    {l : Level} (m : Model l) -> Model-Morphism initial-model m
  initial-model-morphism m =
    record {
      C = C;
      S = S;
      T = T;
      E = E;
      preserve-[] = refl;
      preserve-extend = λ Γ A -> refl;
      preserve-id = refl;
      preserve-compose = λ σ δ -> refl;
      preserve-ε = λ {Γ} -> subst-filler (λ Δ -> C Γ ↣ Δ) refl ε;
      preserve-p = λ {Γ} {A} -> subst-filler (λ Δ -> Δ ↣ C Γ) refl (p (T A));
      preserve-subst-extend =
        λ {Δ} σ a -> subst-filler (λ Θ -> C Δ ↣ Θ) refl (S σ + E a);
      preserve-arrow = λ A B -> refl;
      preserve-bool = refl;
      preserve-subst-action = λ a σ -> refl;
      preserve-q =
        λ {Γ A} -> subst-filler (λ Δ -> Elem Δ (T A)) refl q;
      preserve-abs =
        λ {Γ A B} a i ->
          subst-filler (λ D -> Elem (C Γ) D) refl
            (cong abs (subst-filler (λ Δ -> Elem Δ (T B)) refl (E a)) i) i ;
      preserve-app =
        λ {Γ A B} a b ->
          cong (λ c -> app c (E b))
               (subst-filler (Elem (C Γ)) refl (E a));
      preserve-true = λ {Γ} -> subst-filler (λ A -> Elem (C Γ) A) refl true;
      preserve-false = λ {Γ} -> subst-filler (λ A -> Elem (C Γ) A) refl false;
      preserve-brec =
        λ {Γ} A a b i ->
          subst-filler (λ B -> Elem (C Γ) B) refl
            (subst-filler (λ B -> Elem (C Γ) (arrow B (T A))) refl
              (brec (T A) (E a) (E b)) i) i

    }
    where
    open Model m
    T : Initial.Typ -> Typ
    T Initial.bool = bool
    T (Initial.arrow A B) = arrow (T A) (T B)
    C : Initial.Context -> Context
    C Initial.[] = []
    C (Γ Initial.⊹ A) = C Γ ⊹ T A
    S : {Γ Δ : Initial.Context} -> Initial._↣_ Γ Δ -> C Γ ↣ C Δ
    E : {Γ : Initial.Context} {A : Initial.Typ} -> Initial.Elem Γ A -> Elem (C Γ) (T A)
    S Initial.id = id
    S (σ Initial.∘ δ) = S σ ∘ S δ
    S (Initial.left-identity σ i) = left-identity (S σ) i
    S (Initial.right-identity σ i) = right-identity (S σ) i
    S (Initial.associativity σ δ θ i) = associativity (S σ) (S δ) (S θ) i
    S Initial.ε = ε
    S (Initial.ε-unique σ i) = ε-unique (S σ) i
    S (Initial.p A) = p (T A)
    S (σ Initial.+ x) = S σ + E x
    S (Initial.weakening σ a i) = weakening (S σ) (E a) i
    S (Initial.subst-+ σ δ a i) = subst-+ (S σ) (S δ) (E a) i
    S (Initial.p-q-identity i) = p-q-identity i
    S (Initial.is-set σ δ p q i j) =
        subst-is-set (S σ) (S δ) (λ i -> S (p i)) (λ i -> S (q i)) i j
    E (a Initial.[ σ ]) = E a [ S σ ]
    E (Initial.elem-action-identity a i) = elem-action-identity (E a) i
    E (Initial.elem-action-associativity σ δ a i) = elem-action-associativity (S σ) (S δ) (E a) i
    E Initial.q = q
    E (Initial.var σ a i) = var (S σ) (E a) i
    E (Initial.abs a) = abs (E a)
    E (Initial.app a b) = app (E a) (E b)
    E (Initial.subst-abs σ a i) = subst-abs (S σ) (E a) i
    E (Initial.subst-app σ a b i) = subst-app (S σ) (E a) (E b) i
    E (Initial.arrow-beta a b i) = arrow-beta (E a) (E b) i
    E (Initial.arrow-eta a i) = arrow-eta (E a) i
    E Initial.true = true
    E Initial.false = false
    E (Initial.brec A a b) = brec (T A) (E a) (E b)
    E (Initial.subst-true σ i) = subst-true (S σ) i
    E (Initial.subst-false σ i) = subst-false (S σ) i
    E (Initial.subst-brec σ a b i) = subst-brec (S σ) (E a) (E b) i
    E (Initial.bool-beta-true a b i) = bool-beta-true (E a) (E b) i
    E (Initial.bool-beta-false a b i) = bool-beta-false (E a) (E b) i
    E (Initial.is-set a b p q i j) =
        elem-is-set (E a) (E b) (λ i -> E (p i)) (λ i -> E (q i)) i j

  module Reducibility where

    variable
      l : Level

    record Ctx (m : Model l) : Set (lsuc l) where
      open Model m
      field
        obj : Context
        fib : ∣ obj ∣ -> Set l
        is-set : (g : ∣ obj ∣) -> isSet (fib g)

    pattern _/_ obj fib = record { obj = obj; fib = fib }

    Subst : (m : Model l) -> Ctx m -> Ctx m -> Set l
    Subst m Γ Δ =
        Σ ((Ctx.obj Γ) ↣ (Ctx.obj Δ))
          (λ obj -> (g : ∣ Ctx.obj Γ ∣) -> Ctx.fib Γ g -> Ctx.fib Δ (obj ∘ g))
      where open Model m

    subst-path :
      {m : Model l} {Γ Δ : Ctx m} {σ δ : Subst m Γ Δ} (p1 : fst σ ≡ fst δ)
        (p2 : (g : Model.∣_∣ m (Ctx.obj Γ)) -> (g' : Ctx.fib Γ g) ->
               PathP (λ i -> Ctx.fib Δ (Model._∘_ m (p1 i) g)) (snd σ g g') (snd δ g g')) ->
          σ ≡ δ
    subst-path {l} {m} {Γ / Γ'} {Δ / Δ'} {σ , σ'} {δ , δ'} p1 p2 i =
        (p1 i , λ g g' -> p2 g g' i)
      where open Model m

    record Ty (m : Model l) : Set (lsuc l) where
      open Model m
      field
        obj : Typ
        fib : Elem [] obj -> Set l
        is-set : (g : Elem [] obj) -> isSet (fib g)

    record Elm (m : Model l) (Γ : Ctx m) (A : Ty m) : Set (lsuc l) where
      open Model m
      field
        obj : Elem (Ctx.obj Γ) (Ty.obj A)
        fib : (g : ∣ Ctx.obj Γ ∣) -> Ctx.fib Γ g -> Ty.fib A (obj [ g ])

    elm-path :
      {m : Model l} {Γ : Ctx m} {A : Ty m} {a b : Elm m Γ A} (p1 : Elm.obj a ≡ Elm.obj b)
        (p2 : (g : Model.∣_∣ m (Ctx.obj Γ)) -> (g' : Ctx.fib Γ g) ->
               PathP (λ i -> Ty.fib A (Model._[_] m (p1 i) g)) (Elm.fib a g g') (Elm.fib b g g')) ->
          a ≡ b
    elm-path {l} {m} {Γ / Γ'} {A / A'} {a / a'} {b / b'} p1 p2 i =
      record
        { obj = p1 i ;
          fib = λ g g' -> p2 g g' i }
      where open Model m

    Subst-is-set : (m : Model l) -> {Γ Δ : Ctx m} -> isSet (Subst m Γ Δ)
    Subst-is-set m {Γ} {Δ} (σ , σ') (δ , δ') p1 p2 i j =
        let obj : (λ k → fst (p1 k)) ≡ (λ k → fst (p2 k))
            obj = subst-is-set σ δ (λ k -> fst (p1 k)) (λ k -> fst (p2 k))
        in
        let fib : ?
            fib = ?
        in
        obj i j ,
        λ g g' -> {!!}
{-
          Ctx.is-set Δ (obj i j ∘ g)
            (transp (λ l -> Ctx.fib Δ (obj i (j ∧ l) ∘ g)) (~ j) (σ' g g'))
            (transp (λ l -> Ctx.fib Δ (obj i (j ∨ (~ l)) ∘ g)) j (δ' g g'))
            {!transp (λ m -> PathP (λ k -> Ctx.fib Δ (obj (i ∧ m) (((~ m) ∧ k) ∨ (m ∧ j)) ∘ g))
                              (transp (λ l -> Ctx.fib Δ (obj (i ∧ m) (j ∧ l) ∘ g)) (~ j) (σ' g g'))
                              (transp (λ l -> Ctx.fib Δ (obj (i ∧ m) (j ∨ (~ l)) ∘ g)) j (δ' g g')))
                    (~ i) (λ k -> snd (p1 k) g g')!}
            {!
   Ctx.fib Δ
   (subst-is-set σ δ (λ k₁ → fst (p1 k₁)) (λ k₁ → fst (p2 k₁))
    (i ∧ i0) j
    ∘ g) !} i j
-}
      where open Model m
{- PathP (λ k -> Ctx.fib Δ (fst (p1 k) ∘ g)) (σ' g g') (δ g g')
   PathP (λ k -> Ctx.fib Δ ((obj i j) ∘ g))
     (transp (λ l -> Ctx.fib Δ (obj i (j ∧ l) ∘ g)) (~ j) (σ' g g'))
     (transp (λ l -> Ctx.fib Δ (obj i (j ∨ (~ l)) ∘ g)) j (δ' g g'))

   fst (p1 k)
   obj i k

   λ k -> transp (λ l -> Ctx.fib Δ (obj i (((j ∧ l) ∨ k) ∧ ((~ k) ∨ (j ∨ (~ l)))) ∘ g))
            (((~ j) ∨ k) ∧ ((~ k) ∨ j)) (snd (p1 k) g g')
 -}

    foo : (m : Model l) -> {Γ Δ : Ctx m} -> (σ : Subst m Γ Δ) -> (δ : Subst m Γ Δ) -> σ ≡ δ -> σ ≡ δ -> I -> I -> {!!}
    foo m σ δ p q i j = {!fst (Subst-is-set m σ δ p q i j)!}
{-
    Elm-is-set : (m : Model l) -> {Γ : Ctx m} -> {A : Ty m} -> isSet (Elm m Γ A)
    Elm-is-set m {Γ} {A} =
        isSetRetract
          (λ (a / a') -> a , a') (λ (a , a') -> record { obj = a ; fib = a' })
          (λ _ -> refl) (isSetΣ elem-is-set (λ x -> isSetΠ2 (λ g g' -> Ty.is-set A (x [ g ]))))
      where open Model m

    empt : (m : Model l) -> Ctx m
    empt m =
      record
        { obj = [] ;
          fib = λ _ -> Lift ⊤ ;
          is-set = λ _ -> isProp→isSet (λ _ _ -> refl) }
      where open Model m

    ext : (m : Model l) -> Ctx m -> Ty m -> Ctx m
    ext m Γ A =
      record
        { obj = Ctx.obj Γ ⊹ Ty.obj A ;
          fib = λ g -> (Σ (Ctx.fib Γ (p (Ty.obj A) ∘ g)) (λ g' -> Ty.fib A (q [ g ]))) ;
          is-set = λ g -> isSetΣ (Ctx.is-set Γ (p (Ty.obj A) ∘ g)) (λ _ -> Ty.is-set A (q [ g ])) }
      where open Model m

    subst-id : (m : Model l) {Γ : Ctx m} -> Subst m Γ Γ
    subst-id m {Γ / Γ'} =
      record
       { obj = id ;
         fib = λ g g' -> subst⁻ Γ' (left-identity g) g' }
      where open Model m

    compose : (m : Model l) {Γ Δ Θ : Ctx m} -> Subst m Δ Θ -> Subst m Γ Δ -> Subst m Γ Θ
    compose m {Γ / Γ'} {Δ / Δ'} {Θ / Θ'} (σ / σ') (δ / δ') =
      record
        { obj = σ ∘ δ ;
          fib = λ g g' ->
                  subst⁻ Θ' (associativity σ δ g)
                    (σ' (δ ∘ g) (δ' g g')) }
      where open Model m

    id-left-identity :
      (m : Model l) -> {Γ Δ : Ctx m} (σ : Subst m Γ Δ) ->
      compose m (subst-id m) σ ≡ σ
    id-left-identity {l} m {Γ / Γ'} {Δ / Δ'} (σ / σ') =
        subst-path (left-identity σ) λ g g' ->
          substPathP⁻ Δ' (associativity id σ g)
            (substPathP⁻ Δ' (left-identity (σ ∘ g))
              (isSetPathP subst-is-set Δ' refl refl))
      where open Model m

    id-right-identity :
      (m : Model l) -> {Γ Δ : Ctx m} (σ : Subst m Γ Δ) ->
      compose m σ (subst-id m) ≡ σ
    id-right-identity {l} m {Γ / Γ'} {Δ / Δ'} (σ / σ') =
        subst-path (right-identity σ) λ g g' ->
          substPathP⁻ Δ' (associativity σ id g)
            (isSetPathP subst-is-set Δ' ((cong (_∘_ σ) (left-identity g)))
               (slicePathP Γ' (λ δ -> Δ' (σ ∘ δ)) σ' (left-identity g)
                  (substPathP⁻ Γ' (left-identity g)
                     (rcancelPathP Γ' refl))))
      where open Model m

    subst-associativity :
      (m : Model l) -> {Γ Δ Θ Ψ : Ctx m} (σ : Subst m Θ Ψ) (δ : Subst m Δ Θ) (θ : Subst m Γ Δ) ->
      compose m (compose m σ δ) θ ≡ compose m σ (compose m δ θ)
    subst-associativity m {Γ / Γ'} {Δ / Δ'} {Θ / Θ'} {Ψ / Ψ'} (σ / σ') (δ / δ') (θ / θ') =
        subst-path (associativity σ δ θ) λ g g' ->
          substPathP⁻ Ψ' (associativity (σ ∘ δ) θ g)
            (substPathP⁻ Ψ' (associativity σ δ (θ ∘ g))
               (symPathP Ψ' (substPathP⁻ Ψ' (associativity σ (δ ∘ θ) g)
                 (isSetPathP subst-is-set Ψ' (cong (_∘_ σ) (associativity δ θ g))
                    (slicePathP Θ' (λ δ -> Ψ' (σ ∘ δ)) σ' (associativity δ θ g)
                      (substPathP⁻ Θ' (associativity δ θ g)
                        (rcancelPathP Θ' refl)))))))
      where open Model m

    subst-empty : (m : Model l) {Γ : Ctx m} -> Subst m Γ (empt m)
    subst-empty m {Γ / Γ'} =
      record
        { obj = ε ;
          fib = λ g g' -> lift tt }
      where open Model m

    subst-empty-unique :
      (m : Model l) {Γ : Ctx m} (σ : Subst m Γ (empt m)) -> σ ≡ subst-empty m
    subst-empty-unique m {Γ / Γ'} (σ / σ') i =
      record
        { obj = ε-unique σ i ;
          fib = λ g g' -> lift tt }
      where open Model m

    subst-p : (m : Model l) {Γ : Ctx m} (A : Ty m) -> Subst m (ext m Γ A) Γ
    subst-p m {Γ / Γ'} (A / A') =
      record
        { obj = p A;
          fib = λ g g' -> fst g' }
      where open Model m

    subst-ext : (m : Model l) {Δ Γ : Ctx m} {A : Ty m} -> Subst m Δ Γ -> Elm m Δ A -> Subst m Δ (ext m Γ A)
    subst-ext m {Δ / Δ'} {Γ / Γ'} {A / A'} (σ / σ') (a / a') =
      record
        { obj = σ + a ;
          fib =
            λ g g' ->
              subst Γ' (associativity (p A) (σ + a) g)
                (subst⁻ (λ δ -> Γ' (δ ∘ g)) (weakening σ a) (σ' g g')) ,
              subst A' (elem-action-associativity (σ + a) g q)
                (subst⁻ (λ b -> A' (b [ g ])) (var σ a) (a' g g')) }
      where open Model m

    subst-weakening :
      (m : Model l) {Γ Δ : Ctx m} {A : Ty m} (σ : Subst m Γ Δ) (a : Elm m Γ A) ->
        compose m (subst-p m A) (subst-ext m σ a) ≡ σ
    subst-weakening m {Γ / Γ'} {Δ / Δ'} {A / A'} (σ / σ') (a / a') =
        subst-path (weakening σ a) λ g g' ->
          substPathP⁻ Δ' (associativity (p A) (σ + a) g)
            (substPathP Δ' (associativity (p A) (σ + a) g)
               (substPathP⁻ Δ' (cong (λ δ → δ ∘ g) (weakening σ a))
                  (isSetPathP subst-is-set Δ' refl refl)))
      where open Model m

    elem-action : (m : Model l) -> {Δ Γ : Ctx m} {A : Ty m} -> Elm m Γ A -> Subst m Δ Γ -> Elm m Δ A
    elem-action m {Δ / Δ'} {Γ / Γ'} {A / A'} (a / a') (σ / σ') =
      record
        { obj = a [ σ ] ;
          fib =
            λ g g' ->
              subst⁻ A' (elem-action-associativity σ g a)
                (a' (σ ∘ g) (σ' g g')) }
      where open Model m

    subst-compose-ext :
      (m : Model l) -> {Γ Δ Θ : Ctx m} {A : Ty m} (σ : Subst m Γ Δ) (δ : Subst m Θ Γ) (a : Elm m Γ A) ->
        compose m (subst-ext m σ a) δ
        ≡ subst-ext m (compose m σ δ) (elem-action m a δ)
    subst-compose-ext m {Γ / Γ'} {Δ / Δ'} {Θ / Θ'} {A / A'} (σ / σ') (δ / δ') (a / a') =
        subst-path (subst-+ σ δ a) λ g g' ->
          substPathP⁻ (λ θ → Σ (Δ' (p A ∘ θ)) (λ s₁ → A' (q [ θ ]))) (associativity (σ + a) δ g)
              (ΣPathP ( λ θ → Δ' (p A ∘ θ)) (λ θ _ → A' (q [ θ ]))
               (substPathP Δ' (associativity (p A) (σ + a) (δ ∘ g))
                 (substPathP⁻ Δ' (cong (λ θ → θ ∘ (δ ∘ g)) (weakening σ a))
                   (symPathP Δ' (substPathP Δ' (associativity (p A) ((σ ∘ δ) + (a [ δ ])) g)
                     (substPathP⁻ Δ'
                        (cong (λ θ → θ ∘ g) (weakening (σ ∘ δ) (a [ δ ])))
                          (substPathP⁻ Δ' (associativity σ δ g)
                            (isSetPathP subst-is-set Δ' refl refl)))))))
               (substPathP A' (elem-action-associativity (σ + a) (δ ∘ g) q)
                  (substPathP⁻ A' (cong (λ b → b [ δ ∘ g ]) (var σ a))
                     (symPathP A'
                        (substPathP A' (elem-action-associativity ((σ ∘ δ) + (a [ δ ])) g q)
                           (substPathP⁻ A' (cong (λ b → b [ g ]) (var (σ ∘ δ) (a [ δ ])))
                              (substPathP⁻ A' (elem-action-associativity δ g a)
                                 (isSetPathP elem-is-set A' refl refl))))))))
      where open Model m

    elem-act-identity :
      (m : Model l) -> {Γ : Ctx m} {A : Ty m} (a : Elm m Γ A) ->
        elem-action m a (subst-id m) ≡ a
    elem-act-identity m {Γ / Γ'} {A / A'} (a / a') =
        elm-path (elem-action-identity a) λ g g' ->
          substPathP⁻ A' (elem-action-associativity id g a)
            (isSetPathP elem-is-set A' (cong (λ θ -> a [ θ ]) (left-identity g))
               (slicePathP Γ' (λ θ -> A' (a [ θ ])) a' (left-identity g)
                  (substPathP⁻ Γ' (left-identity g)
                        (rcancelPathP Γ' refl))))
      where open Model m

    elem-act-associativity :
      (m : Model l) -> {Γ Δ Θ : Ctx m} {A : Ty m} (σ : Subst m Γ Δ) (δ : Subst m Θ Γ) (a : Elm m Δ A) ->
        elem-action m (elem-action m a σ) δ ≡ elem-action m a (compose m σ δ)
    elem-act-associativity m {Γ / Γ'} {Δ / Δ'} {Θ / Θ'} {A / A'} (σ / σ') (δ / δ') (a / a') =
        elm-path (elem-action-associativity σ δ a) (λ g g' ->
          substPathP⁻ A' (elem-action-associativity δ g (a [ σ ]))
            (substPathP⁻ A' (elem-action-associativity σ (δ ∘ g) a)
              (symPathP A'
                 (substPathP⁻ A' (elem-action-associativity (σ ∘ δ) g a)
                    (isSetPathP elem-is-set A' (cong (λ θ -> a [ θ ]) (associativity σ δ g))
                       (slicePathP Δ' (λ θ -> A' (a [ θ ])) a' (associativity σ δ g)
                          (substPathP⁻ Δ' (associativity σ δ g)
                             (rcancelPathP Δ' refl))))))))
      where open Model m

    elem-q : (m : Model l) {Γ : Ctx m} {A : Ty m} -> Elm m (ext m Γ A) A
    elem-q m {Γ / Γ'} {A / A'} =
      record
        { obj = q ;
          fib = λ g g' -> snd g' }
      where open Model m

    q-var : (m : Model l) {Γ Δ : Ctx m} {A : Ty m} (σ : Subst m Γ Δ) (a : Elm m Γ A) ->
      elem-action m (elem-q m {Δ} {A}) (subst-ext m σ a) ≡ a
    q-var m {Γ / Γ'} {Δ / Δ'} {A / A'} (σ / σ') (a / a') =
        elm-path (var σ a) λ g g' ->
          substPathP⁻ A' (elem-action-associativity (σ + a) g q)
            (substPathP A' (elem-action-associativity (σ + a) g q)
               (substPathP⁻ A' (cong (λ b → b [ g ]) (var σ a))
                  ((isSetPathP elem-is-set A' refl refl))))
      where open Model m

    subst-p-q-identity : (m : Model l) {Γ : Ctx m} {A : Ty m} ->
      subst-ext m (subst-p m {Γ} A) (elem-q m {Γ} {A}) ≡ subst-id m
    subst-p-q-identity m {Γ / Γ'} {A / A'} =
        subst-path p-q-identity λ g g' ->
          ΣPathP (λ σ → Γ' (p A ∘ (σ ∘ g))) (λ σ _ → A' (q [ σ ∘ g ]))
            (substPathP Γ' (associativity (p A) (p A + q) g)
               (substPathP⁻ Γ' (cong (λ σ → σ ∘ g) (weakening (p A) q))
                  (symPathP Γ'
                     (substPathP⁻ Γ' (cong (λ σ → p A ∘ σ) (left-identity g))
                        (isSetPathP subst-is-set Γ' refl refl)))))
            (substPathP A' (elem-action-associativity (p A + q) g q)
               (substPathP⁻ A' (cong (λ b → b [ g ]) (var (p A) q))
                  (symPathP A'
                     (substPathP⁻ A' (cong (λ σ → q [ σ ]) (left-identity g))
                        (isSetPathP elem-is-set A' refl refl)))))
      where open Model m

    typ-arrow : (m : Model l) -> Ty m -> Ty m -> Ty m
    typ-arrow m A B =
      record
        { obj = arrow (Ty.obj A) (Ty.obj B);
          fib = λ g -> (u : Elem [] (Ty.obj A)) (u' : Ty.fib A u) -> Ty.fib B (app g u) ;
          is-set = λ g -> isSetΠ2 (λ u u' -> Ty.is-set  B (app g u)) }
      where open Model m

    elem-abs : (m : Model l) {Γ : Ctx m} {A B : Ty m} ->
      Elm m (ext m Γ A) B -> Elm m Γ (typ-arrow m A B)
    elem-abs m {Γ / Γ'} {A / A'} {B / B'} (a / a') =
      record
         { obj = abs a ;
           fib = λ g g' u u' ->
                   subst⁻ (λ b -> B' (app b u)) (subst-abs g a)
                     (subst⁻ B' (arrow-beta (a [ (g ∘ p A) + q ]) u)
                        (subst⁻ B' (elem-action-associativity ((g ∘ p A) + q) (id + u) a)
                           (subst⁻ (λ σ → B' (a [ σ ])) (subst-+ (g ∘ p A) (id + u) q)
                             (subst⁻ (λ σ → B' (a [ ((g ∘ p A) ∘ (id + u)) + σ ])) (var id u)
                                (subst⁻ (λ σ → B' (a [ σ + u ])) (associativity g (p A) (id + u))
                                   (subst⁻ (λ σ → B' (a [ (g ∘ σ) + u ])) (weakening id u)
                                     (subst⁻ (λ σ → B' (a [ σ + u ])) (right-identity g)
                                        (a' (g + u)
                                           (subst⁻ Γ' (weakening g u) g' ,
                                            subst⁻ A' (var g u) u'))))))))) }
      where open Model m

    elem-app : (m : Model l) {Γ : Ctx m} {A B : Ty m} ->
      Elm m Γ (typ-arrow m A B) -> Elm m Γ A -> Elm m Γ B
    elem-app m {Γ / Γ'} {A / A'} {B / B'} (a / a') (b / b') =
      record
        { obj = app a b ;
          fib = λ g g' ->
            subst⁻ B' (subst-app g a b)
              (a' g g' (b [ g ]) (b' g g')) }
      where open Model m

    subst-elem-abs : (m : Model l) {Γ Δ : Ctx m} {A B : Ty m} (σ : Subst m Γ Δ) (a : Elm m (ext m Δ A) B) ->
        elem-action m (elem-abs m {Δ} {A} {B} a) σ
        ≡ elem-abs m {Γ} {A} {B}
            (elem-action m a (subst-ext m (compose m σ (subst-p m {Γ} A)) (elem-q m {Γ} {A})))
    subst-elem-abs m {Γ / Γ'} {Δ / Δ'} {A / A'} {B / B'} (σ / σ') (a / a') =
        elm-path (subst-abs σ a) λ g g' ->
          {!!}
      where open Model m

    subst-elem-app : (m : Model l) {Γ Δ : Ctx m} {A B : Ty m}
      (σ : Subst m Γ Δ) (a : Elm m Δ (typ-arrow m A B)) (b : Elm m Δ A) ->
        elem-action m (elem-app m {Δ} {A} {B} a b) σ
        ≡ elem-app m (elem-action m a σ) (elem-action m b σ)
    subst-elem-app m {Γ / Γ'} {Δ / Δ'} {A / A'} {B / B'} (σ / σ') (a / a') (b / b') =
        elm-path (subst-app σ a b) λ g g' ->
          {!!}
      where open Model m

    typ-arrow-beta : (m : Model l) {Γ : Ctx m} {A B : Ty m} (a : Elm m (ext m Γ A) B) (b : Elm m Γ A) ->
        elem-app m (elem-abs m {Γ} {A} {B} a) b
        ≡ elem-action m a (subst-ext m (subst-id m) b)
    typ-arrow-beta m {Γ / Γ'} {A / A'} {B / B'} (a / a') (b / b') =
        elm-path (arrow-beta a b) λ g g' ->
          {!!}
      where open Model m

    typ-arrow-eta : (m : Model l) {Γ : Ctx m} {A B : Ty m} (a : Elm m Γ (typ-arrow m A B)) ->
        a ≡ elem-abs m {Γ} {A} {B} (elem-app m {ext m Γ A} {A} {B}
              (elem-action m a (subst-p m A)) (elem-q m {Γ} {A}))
    typ-arrow-eta m {Γ / Γ'} {A / A'} {B / B'} (a / a') =
        elm-path (arrow-eta a) λ g g' ->
          {!!}
      where open Model m

    typ-bool : (m : Model l) -> Ty m
    typ-bool m =
      record
        { obj = bool;
          fib = λ g -> (g ≡ true) ⊎ (g ≡ false) ;
          is-set = λ g ->
            isSet⊎ (isProp→isSet (isOfHLevelPath' 1 elem-is-set g true))
                   (isProp→isSet (isOfHLevelPath' 1 elem-is-set g false)) }
      where open Model m

    elem-true : (m : Model l) {Γ : Ctx m} -> Elm m Γ (typ-bool m)
    elem-true m {Γ / Γ'} =
       record
         { obj = true ;
           fib = λ g g' -> inl (subst-true g) }
      where open Model m

    elem-false : (m : Model l) {Γ : Ctx m} -> Elm m Γ (typ-bool m)
    elem-false m {Γ / Γ'} =
      record
         { obj = false ;
           fib = λ g g' -> inr (subst-false g) }
      where open Model m

    elem-brec : (m : Model l) {Γ : Ctx m} ->
      (A : Ty m) -> Elm m Γ A -> Elm m Γ A -> Elm m Γ (typ-arrow m (typ-bool m) A)
    elem-brec m {Γ / Γ'} (A / A') (a / a') (b / b') =
      record
         { obj = brec A a b ;
           fib = λ { g g' u (inl u') ->
                       subst⁻ (λ c -> A' (app c u)) (subst-brec g a b)
                         (subst⁻ (λ c -> A' (app (brec A (a [ g ]) (b [ g ])) c)) u'
                            (subst⁻ A' (bool-beta-true (a [ g ]) (b [ g ]))
                               (a' g g'))) ;
                     g g' u (inr u') ->
                       subst⁻ (λ c -> A' (app c u)) (subst-brec g a b)
                         (subst⁻ (λ c -> A' (app (brec A (a [ g ]) (b [ g ])) c)) u'
                            (subst⁻ A' (bool-beta-false (a [ g ]) (b [ g ]))
                               (b' g g'))) }}
      where open Model m

    subst-elem-true : (m : Model l) {Γ Δ : Ctx m} (σ : Subst m Γ Δ) ->
        elem-action m (elem-true m) σ ≡ elem-true m
    subst-elem-true m {Γ / Γ'} {Δ / Δ'} (σ / σ') =
        {!!}
      where open Model m

    subst-elem-false : (m : Model l) {Γ Δ : Ctx m} (σ : Subst m Γ Δ) ->
        elem-action m (elem-false m) σ ≡ elem-false m
    subst-elem-false m {Γ / Γ'} {Δ / Δ'} (σ / σ') =
        {!!}
      where open Model m

    subst-elem-brec : (m : Model l) {Γ Δ : Ctx m} {A : Ty m}
      (σ : Subst m Γ Δ) (a : Elm m Δ A) (b : Elm m Δ A) ->
        elem-action m (elem-brec m A a b) σ
        ≡ elem-brec m A (elem-action m a σ) (elem-action m b σ)
    subst-elem-brec m {Γ / Γ'} {Δ / Δ'} {A / A'} (σ / σ') (a / a') (b / b') =
        {!!}
      where open Model m

    typ-bool-beta-true :
        (m : Model l) {Γ : Ctx m} {A : Ty m} (a : Elm m Γ A) (b : Elm m Γ A) ->
        elem-app m (elem-brec m A a b) (elem-true m) ≡ a
    typ-bool-beta-true m =
        {!!}
      where open Model m

    typ-bool-beta-false :
        (m : Model l) {Γ : Ctx m} {A : Ty m} (a : Elm m Γ A) (b : Elm m Γ A) ->
        elem-app m (elem-brec m A a b) (elem-false m) ≡ b
    typ-bool-beta-false m =
        {!!}
      where open Model m

  reducibility-model : {l : Level} -> Model l -> Model (lsuc l)
  reducibility-model m =
    record {
      Context = Ctx m;
      _↣_ = Subst m;
      Typ = Ty m;
      Elem = Elm m;
      subst-is-set = Subst-is-set m;
      elem-is-set = Elm-is-set m;
      [] = empt m;
      _⊹_ = ext m;
      id = subst-id m;
      _∘_ = compose m;
      left-identity = id-left-identity m;
      right-identity = id-right-identity m;
      associativity = subst-associativity m;
      ε = subst-empty m;
      ε-unique = subst-empty-unique m;
      p = subst-p m;
      _+_ = subst-ext m;
      weakening = subst-weakening m;
      arrow = typ-arrow m;
      bool = typ-bool m;
      _[_] = elem-action m;
      subst-+ = subst-compose-ext m;
      elem-action-identity = elem-act-identity m;
      elem-action-associativity = elem-act-associativity m;
      q = λ {Γ} {A} -> elem-q m {Γ} {A};
      var = q-var m;
      p-q-identity = λ {Γ} {A} -> subst-p-q-identity m {Γ} {A};
      abs = λ {Γ} {A} {B} -> elem-abs m {Γ} {A} {B};
      app = elem-app m;
      subst-abs = λ {Γ} {Δ} {A} {B} -> subst-elem-abs m {Γ} {Δ} {A} {B};
      subst-app = subst-elem-app m;
      arrow-beta = typ-arrow-beta m;
      arrow-eta = λ {Γ} {A} {B} -> typ-arrow-eta m {Γ} {A} {B};
      true = elem-true m;
      false = elem-false m;
      brec = elem-brec m;
      subst-true = subst-elem-true m;
      subst-false = subst-elem-false m;
      subst-brec = subst-elem-brec m;
      bool-beta-true = typ-bool-beta-true m;
      bool-beta-false = typ-bool-beta-false m
    }
    where open Reducibility

  initial-reducibility-model : Model (lsuc lzero)
  initial-reducibility-model = reducibility-model initial-model

  initial-reducibility-morphism : Model-Morphism initial-model initial-reducibility-model
  initial-reducibility-morphism = initial-model-morphism initial-reducibility-model

  typ-obj-identity : (A : Initial.Typ) ->
     Reducibility.Ty.obj (Model-Morphism.T initial-reducibility-morphism A) ≡ A
  typ-obj-identity (Initial.arrow A B) i = Initial.arrow (typ-obj-identity A i) (typ-obj-identity B i)
  typ-obj-identity Initial.bool i = Initial.bool

  ctx-obj-identity : (Γ : Initial.Context) ->
     Reducibility.Ctx.obj (Model-Morphism.C initial-reducibility-morphism Γ) ≡ Γ
  ctx-obj-identity Initial.[] i = Initial.[]
  ctx-obj-identity (Γ Initial.⊹ A) i = ctx-obj-identity Γ i Initial.⊹ typ-obj-identity A i 

  subst-obj-identity : {Γ Δ : Initial.Context} (σ : Γ Initial.↣ Δ) ->
     PathP (λ i -> (ctx-obj-identity Γ i) Initial.↣ (ctx-obj-identity Δ i))
       (fst (Model-Morphism.S initial-reducibility-morphism σ))
       σ
  elem-obj-identity : {Γ : Initial.Context} {A : Initial.Typ} (a : Initial.Elem Γ A) ->
     PathP (λ i -> Initial.Elem (ctx-obj-identity Γ i) (typ-obj-identity A i))
       (Reducibility.Elm.obj (Model-Morphism.E initial-reducibility-morphism a))
       a
  subst-obj-identity Initial.id i = Initial.id
  subst-obj-identity (σ Initial.∘ δ) i =
    (subst-obj-identity σ i) Initial.∘ (subst-obj-identity δ i)
  subst-obj-identity (Initial.right-identity σ j) i =
    Initial.right-identity (subst-obj-identity σ i) j
  subst-obj-identity (Initial.associativity σ δ θ j) i =
    Initial.associativity
       (subst-obj-identity σ i)
       (subst-obj-identity δ i)
       (subst-obj-identity θ i) j
  subst-obj-identity Initial.ε i = Initial.ε
  subst-obj-identity (Initial.ε-unique σ j) i =
    Initial.ε-unique (subst-obj-identity σ i) j
  subst-obj-identity (Initial.p A) i = Initial.p (typ-obj-identity A i)
  subst-obj-identity (σ Initial.+ a) i =
    (subst-obj-identity σ i) Initial.+ (elem-obj-identity a i)
  subst-obj-identity (Initial.weakening σ a j) i =
    Initial.weakening (subst-obj-identity σ i) (elem-obj-identity a i) j
  subst-obj-identity (Initial.subst-+ σ δ a j) i =
    Initial.subst-+
      (subst-obj-identity σ i)
      (subst-obj-identity δ i)
      (elem-obj-identity a i) j
  subst-obj-identity (Initial.p-q-identity j) i = Initial.p-q-identity j
  subst-obj-identity (Initial.is-set σ δ p q j k) = {!!}
{-
    Initial.is-set
      (subst-obj-identity σ i)
      (subst-obj-identity δ i)
      (λ l -> subst-obj-identity (p l) i)
      (λ l -> subst-obj-identity (q l) i)
      j k
-}
  subst-obj-identity (Initial.left-identity σ j) i = {!
         (Model-Morphism.S initial-reducibility-morphism
          (Initial.left-identity σ j))!}

    {- Initial.left-identity (subst-obj-identity σ i) j -}
  elem-obj-identity (a Initial.[ σ ]) i = {!!}
  elem-obj-identity (Initial.elem-action-identity a j) i = {!!}
  elem-obj-identity (Initial.elem-action-associativity σ δ a j) i = {!!}
  elem-obj-identity Initial.q i = {!!}
  elem-obj-identity (Initial.var σ a j) i = {!!}
  elem-obj-identity (Initial.abs a) i = {!!}
  elem-obj-identity (Initial.app a b) i = {!!}
  elem-obj-identity (Initial.subst-abs σ a j) i = {!!}
  elem-obj-identity (Initial.subst-app σ a b j) i = {!!}
  elem-obj-identity (Initial.arrow-beta a b j) i = {!!}
  elem-obj-identity (Initial.arrow-eta a j) i = {!!}
  elem-obj-identity Initial.true i = {!!}
  elem-obj-identity Initial.false i = {!!}
  elem-obj-identity (Initial.brec A a b) i = {!!}
  elem-obj-identity (Initial.subst-true σ j) i = {!!}
  elem-obj-identity (Initial.subst-false σ j) i = {!!}
  elem-obj-identity (Initial.subst-brec σ a b j) i = {!!}
  elem-obj-identity (Initial.bool-beta-true a b j) i = {!!}
  elem-obj-identity (Initial.bool-beta-false a b j) i = {!!}
  elem-obj-identity (Initial.is-set a b p q j k) i = {!!}

  canonicity-exists :
    (b : Model.Elem initial-model (Model.[] initial-model) (Model.bool initial-model)) ->
    (b ≡ Model.true initial-model) ⊎ (b ≡ Model.false initial-model)
  canonicity-exists b =
    let b' = Model-Morphism.E initial-reducibility-morphism b in
    let b'' = Reducibility.Elm.fib b' in
    let b''' = b'' Initial.id (lift tt) in
    let b'''' = subst (λ a -> (a ≡ Initial.true) ⊎ (a ≡ Initial.false)) (Initial.elem-action-identity _) b''' in
     {!Reducibility.Elm.obj
         (Model-Morphism.E initial-reducibility-morphism b)!}

  canonicity-unique :
    (Model.true initial-model {Model.[] initial-model} ≡ Model.false initial-model) -> ⊥
  canonicity-unique p = {!!}
-}
