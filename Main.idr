import Firth


op : Op [a, String] [Int, String, String]
op = with Firth do
    drop
    dup
    push 1
    push 2
    lessThan
    choose 5 6
    push 3
    swap
    add


test : Stack [String, Int, String, Double]
test = f Firth.Nil where
    f = do
        push 5.2
        push "b"
        push (the (List Int) [1, 2, 3])
        op
        swap


main : IO ()
main = do
    print test
