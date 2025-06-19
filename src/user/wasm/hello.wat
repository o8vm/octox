(module
  ;; システムコール用のインポート関数を定義
  (import "kernel" "syscall" (func $syscall (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (result i32)))
  
  ;; メモリを定義
  (memory 1)
  
  ;; 文字列データ
  (data (i32.const 0) "Hello, World!\n")
  
  ;; メイン関数
  (func $main (export "main") (result i32)
    ;; write(1, "Hello, World!\n", 14) を呼び出す
    (call $syscall
      (i32.const 16)  ;; write システムコール番号
      (i32.const 1)   ;; 標準出力のファイルディスクリプタ
      (i32.const 0)   ;; 文字列の開始アドレス
      (i32.const 14)  ;; 文字列の長さ
      (i32.const 0)   ;; 未使用の引数
      (i32.const 0)   ;; 未使用の引数
      (i32.const 0)   ;; 未使用の引数
    )
  )
)