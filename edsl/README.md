# 插件 EDSL 原型

设计见 [../docs/EDSL.md](../docs/EDSL.md)。同一个 tagless final 签名的两个实现,对同一组示例插件
生成逐字相同的 AST、JS 与分析报告。

| 目录 | 内容 |
|---|---|
| `racket/` | `lang.rkt`(模块语言,展开期检查键)、`sym.rkt`(签名与三个解释)、`examples.rkt`、`bad/`(反例) |
| `ocaml/` | `sym.ml`(签名,键带多态变体幻影类型)、`interp.ml`(三个解释)、`examples.ml`(functor)、`bad/` 与 `negative.ml`(反例) |
| `runtime/rt.js` | 演算语义的 JS 运行时:LIFO 撤销、按令牌撤回、生成器逐步执行、可选依赖、资源 |
| `payload/` | 测试用的载荷 |
| `test/run.js` | 在 rt.js 上跑生成的插件:合流、恢复、可选依赖、反应、撤走提供者、资源不泄漏 |
| `out/` | 生成结果 |

在 WSL 中运行全部检查(需要 racket、opam 的 OCaml 与 dune、node):

```sh
sh check.sh
```

dune 在 `/mnt/d` 上建不了 RPC socket,`check.sh` 把构建目录放到 `/tmp/edsl-ocaml-build`。
