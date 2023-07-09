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

/-
A separate inductive type is required due to occurrence failure (if we attempted to define Value.VFunc : (List Value -> Value) -> Value), the typechecker throws:
> (kernel) arg #1 of 'Value.VCons' has a non positive occurrence of the datatypes being declared

TODO: investigate this further.
-/
inductive HValue where -- HValue essentially stands for (higher-order abstract syntax) value (referring to our encoding of lambdas using Lean4 lambdas)
  | HVal : Value -> HValue
  | HFunc : (List Value -> Value) -> HValue -- Lean4 encoding of lambda values

-- Take an HValue which represents a Value, and return a Value.
def unwrap (hv : HValue) : Except String Value :=
  match hv with
    | HValue.HFunc _ => Except.error "`unwrap` called on `HFunc`, excepted `HVal"
    | HValue.HVal v => pure v

inductive Environment α where
  | ENil : Environment α
  | ECons : Prod String α -> Environment α -> Environment α

def empty_env : Environment HValue := Environment.ENil 

def make_env (v : List (Prod String HValue)) : Environment HValue := match v with
  | [] => empty_env
  | α :: β => Environment.ECons α (make_env β)

-- (Except monad to propagate error)
def apply (e : HValue) (args : List Value) : Except String HValue :=
  match e with
    | HValue.HVal _ => Except.error "HVal provided to `apply`, expected `HFunc`"
    | HValue.HFunc f => pure $ HValue.HVal (f args)

def abstract (xs : List Value) (e : Expr) (env : Environment Value) : List Value -> Env := fun args => eval (defargs env xs args) e

def eval (env : Environment Value) (expr : Expr) : Value :=
  match expr with
  | Expr.Number n => Value.VInt n
  | Expr.Variable v => find env v
  | Expr.If e1 e2 e3 => match (eval env e1) with
    | Value.VBool True => eval env e2
    | Value.VBool False => eval env e3
  | Expr.Apply f es => let ev := fun e1 => eval env e1; apply (eval f env) (map ev es)
  | Expr.Lambda xs e1 => abstract xs e1 env

/-
Theorems
-/