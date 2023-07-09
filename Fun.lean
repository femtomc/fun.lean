/-
abstract syntax for the Fun language
-/

inductive Defn where
  | Val : String -> Expr -> Defn
  | Rec : String -> Expr -> Defn

inductive Expr where
  | Number : Int -> Expr
  | Variable : String -> Expr
  | Apply : Expr -> List Expr -> Expr
  | If : Expr -> Expr -> Expr -> Expr
  | Lambda : List String -> Expr -> Expr
  | Let : Defn -> Expr

inductive Phrase where
  | Calculate : Expr -> Phrase
  | Define : Defn -> Phrase

/-
evaluation semantics
-/

inductive Value where
  | VNil : Value -- the type of the singleton empty list
  | VInt : Int -> Value -- the type of ints
  | VBool : Bool -> Value -- the type of bools
  | VCons : Value -> Value -> Value -- the type of lists
deriving Repr

/-
A separate inductive type is required due to occurrence failure (if we attempted to define Value.VFunc : (List Value -> Value) -> Value), the typechecker throws:
> (kernel) arg #1 of 'Value.VCons' has a non positive occurrence of the datatypes being declared

TODO: investigate this further.
-/
inductive HValue where -- HValue essentially stands for (higher-order abstract syntax) value (referring to our encoding of lambdas using Lean4 lambdas)
  | HVal : Value -> HValue
  | HFunc : (List Value -> Value) -> HValue -- Lean4 encoding of lambda values

instance : Repr HValue where
  reprPrec :=  fun h =>
    match h with
    | HValue.HVal v => reprPrec v
    | HValue.HFunc _ => reprPrec "<lean lambda>"

-- Take an HValue which represents a Value, and return a Value.
def unwrap (hv : HValue) : Except String Value :=
  match hv with
    | HValue.HFunc _ => Except.error "`unwrap` called on `HFunc`, expected `HVal"
    | HValue.HVal v => pure v

inductive Environment α where
  | ENil : Environment α
  | ECons : Prod String α -> Environment α -> Environment α
deriving Repr

def empty_env : Environment HValue := Environment.ENil 

def make_env (v : List (Prod String HValue)) : Environment HValue := 
  match v with
    | [] => empty_env
    | α :: β => Environment.ECons α (make_env β)

def lifted_map (f : α -> Except β γ) (v : List α) : Except β (List γ) := 
  match v with
    | [] => pure []
    | (x :: xs) => let lifted_cons := fun y => 
      match (lifted_map f xs) with
        | Except.ok u => pure (y :: u)
        | Except.error e => Except.error e; 
      (f x) >>= lifted_cons

-- (Except monad to propagate error)
def apply (e : HValue) (args : List HValue) : Except String HValue :=
  match e with
    | HValue.HVal _ => Except.error "HVal provided to `apply`, expected `HFunc`"
    -- TODO: instead of defining `lifted_map`, what's the monadic
    -- idiom?
    | HValue.HFunc f => HValue.HVal <$> (f <$> lifted_map unwrap args)

def eval (env : Environment Value) (expr : Expr) : Except String HValue :=
  match expr with
  | Expr.Number n => pure $ HValue.HVal $ (Value.VInt n)
  | Expr.Variable v => pure $ find env v
  | Expr.If e1 e2 e3 => 
    do let v <- eval env e1
       let q <- unwrap v
        match q with
          | Value.VBool true => eval env e2
          | Value.VBool false => eval env e3
          | _ => Except.error "(Expr.If) Evaluated the branch condition to non-Boolean."

/-
Theorems
-/