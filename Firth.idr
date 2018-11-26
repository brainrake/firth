||| Stack-based concatenative programming (like Forth and Kitten) in Idris
module Firth

%default total

||| The Stack's type is parametrized by the list of the elements' types
data Stack : List Type -> Type where
    -- The empty stack
    Nil : Stack []

    -- Consing an element onto a stack conses the type of the element
    -- onto the list of element types in the stack's type
    (::) : t -> Stack ts -> Stack (t :: ts)


Show (Stack []) where
    show _ = "[]"

(Show (Stack ts), Show t) => Show (Stack (t :: ts)) where
    show (x :: xs) = show x ++ " :: " ++ show xs


||| Append stacks
(++) : Stack as -> Stack bs -> Stack (as ++ bs)
(++) [] ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)


||| The type of a non-polymorphic operation.
||| Takes a stack containing precisely the operation's inputs and
||| returns a stack containing the outputs.
MonoOp : List Type -> List Type -> Type
MonoOp ts1 ts2 = Stack ts1 -> Stack ts2


||| The type of a stack-polymorphic operation.
||| Takes a stack containing the operation's inputs and possibly more elements, and
||| returns a stack containing the outputs and the unconsumed inputs.
Op : { ts : List Type } -> List Type -> List Type -> Type
Op {ts} ts1 ts2 = Stack (ts1 ++ ts) -> Stack (ts2 ++ ts)


step : MonoOp (t1 :: ts1) ts2 -> t1 -> MonoOp ts1 ts2
step f x s =
    f (x :: s)

-- Generalize a non-polymorphic operation to a polymorphic operation.
gen : MonoOp ts1 ts2 -> Op ts1 ts2
gen {ts1} f s =
    case ts1 of
        [] => f [] ++ s
        t :: ts =>
            case s of
                [] impossible
                x :: xs =>
                    gen (f . (x ::)) xs


push' : t -> MonoOp [] [t]
push' x [] = [x]

push : t -> Op [] [t]
push x = gen (push' x)

push'' : t -> Op [] [t]
push'' {t} x = gen (the (MonoOp [] [t]) (\[] => [x]))
-- -- this doesn't work, Idris can't infer the right type for the lambda
-- push'' x = gen (\[] => [x])

drop' : MonoOp [t] []
drop' [x] = []

drop : Op [t] []
drop = gen drop'

dup' : MonoOp [t] [t, t]
dup' [x] = [x, x]

dup : Op [t] [t, t]
dup = gen dup'


choose' : Lazy t -> Lazy t -> MonoOp [Bool] [t]
choose' then_ else_ (b :: xs)  =
    (if b then then_ else else_) :: xs

choose : Lazy t -> Lazy t -> Op [Bool] [t]
choose then_ else_ = gen (choose' then_ else_)

add' : MonoOp [Int, Int] [Int]
add' [x, y] = [x + y]

add : Op [Int, Int] [Int]
add = gen add'

swap' : MonoOp [a, b] [b, a]
swap' [x, y] = [y, x]

swap : Op [a, b] [b, a]
swap = gen swap'

lessThan' : MonoOp [Int, Int] [Bool]
lessThan' [x, y] = [x < y]

lessThan : Op [Int, Int] [Bool]
lessThan = gen lessThan'


||| Fake do syntax
(>>=) : MonoOp ts1 ts2 -> (() -> MonoOp ts2 ts3) -> MonoOp ts1 ts3
(>>=) m f x =
    f () (m x)
