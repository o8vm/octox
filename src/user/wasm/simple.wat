(module
    (import "kernel" "syscall" (func $syscall (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (result i32)))
    
    ;; メモリを定義
    (memory 1)
    
    ;; 文字列データ
    (data (i32.const 0) "Hello from simple.wat\n")
    
    ;; 最もシンプルなmain関数
    (func $main (export "main") (result i32)
        ;; "Hello from simple.wat\n" を出力
        (call $syscall (i32.const 16) (i32.const 1) (i32.const 0) (i32.const 21) (i32.const 0) (i32.const 0) (i32.const 0))
        drop
        
        ;; 0を返す
        i32.const 0
    )
) 