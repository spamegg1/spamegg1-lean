#check -454.2123215
#check (0 : Float)

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
#eval origin
#eval origin.x

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 } -- -6.5, 32.2

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

-- #check { x := 0.0, y := 0.0 } -- error
#check ({ x := 0.0, y := 0.0 } : Point) -- OK
#check { x := 0.0, y := 0.0 : Point} -- OK

def zeroX (p : Point) : Point := { x := 0, y := p.y }
def zeroXbetter (p : Point) : Point := { p with x := 0 }

def fourAndThree : Point := { x := 4.3, y := 3.4 }
#eval fourAndThree
#eval zeroXbetter fourAndThree -- does not mutate!
#eval fourAndThree -- hasn't changed!

#check (Point.mk)
#check Point.mk 1.5 2.8

#eval "one string".append " and another"

def Point.modifyBoth (f : Float -> Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval fourAndThree.modifyBoth Float.floor

-- Define a structure named RectangularPrism that contains
-- the height, width, and depth of a rectangular prism, each as a Float.
structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

-- Define a function named volume : RectangularPrism → Float
-- that computes the volume of a rectangular prism.
def RectangularPrism.volume (rp : RectangularPrism) : Float :=
  rp.width * rp.height * rp.depth

-- Define a structure named Segment that represents a line segment by its endpoints,
structure Segment where
  start : Point
  ending : Point

-- and define a function length : Segment → Float that computes the
-- length of a line segment. Segment should have at most two fields.
def Segment.length (s : Segment) : Float :=
  Float.sqrt (((s.ending.x - s.start.x) ^ 2.0) + ((s.ending.y - s.start.y) ^ 2.0))

-- Which names are introduced by the declaration of RectangularPrism?
-- ANSWER: RP.mk, RP.width, RP.height, RP.depth

-- Which names are introduced by the following declarations of Hamster and Book?
-- What are their types?
structure Hamster where
  name : String
  fluffy : Bool
-- ANSWER: Hamster.mk : String -> Bool -> Hamster
-- Hamster.name : String
-- Hamster.fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float
-- ANSWER: Book.makeBook : String -> String -> Float -> Book
-- Book.title : String
-- Book.author : String
-- Book.price : Float
