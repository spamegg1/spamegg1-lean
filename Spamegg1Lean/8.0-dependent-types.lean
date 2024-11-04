-- Dependent types are types that contain non-type expressions.
def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true  => (3 : Nat)
  | false => "three"

inductive Sign where | pos | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)
