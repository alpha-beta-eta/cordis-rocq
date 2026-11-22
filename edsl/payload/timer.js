"use strict";
// 资源载荷:成对给出 acquire/release。live 只用于测试检查是否泄漏。
let live = 0;
module.exports = {
  acquire(label) { live++; return { label }; },
  release(_h) { live--; },
  live: () => live,
};
