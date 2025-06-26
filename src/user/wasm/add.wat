(module
    ;; add(a, b) returns a+b
    (func $add (export "add") (param $a i32) (param $b i32) (result i32)
        (i32.add (local.get $a) (local.get $b))
    )

    (func $main (export "main") (result i32)
        (call $add (i32.const 1) (i32.const 2)))
)