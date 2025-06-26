(module
    ;; システムコール用のインポート関数を定義
    (import "kernel" "syscall" (func $syscall (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (result i32)))
    
    ;; メモリを定義 (4ページ = 256KB)
    (memory 4)
    
    ;; 文字列データ
    (data (i32.const 0) "Hello\n")
    
    ;; メイン関数
    (func $main (export "main") (result i32)
        (local $counter i32)
        
        ;; カウンターを1で初期化
        (local.set $counter (i32.const 1))
        
        ;; シンプルなループ: 1から3まで
        (loop $simple_loop
            ;; "Hello" を出力
            (call $syscall (i32.const 16) (i32.const 1) (i32.const 0) (i32.const 6) (i32.const 0) (i32.const 0) (i32.const 0))
            drop
            
            ;; カウンターをインクリメント
            (local.set $counter (i32.add (local.get $counter) (i32.const 1)))
            
            ;; カウンターが3以下ならループを続ける
            (i32.le_u (local.get $counter) (i32.const 3))
            br_if $simple_loop
        )
        
        ;; カウンターの最終値を返す
        (local.get $counter)
    )
)