"use strict";
// 工具的执行函数:载荷只拿到参数(这里是工具名),返回一个闭包。
// made 记下工厂被调用的次数,测试用它检查加载期间没有运行载荷代码。
const echo = (name) => { echo.made++; return (args) => `${name} ${args}`; };
echo.made = 0;
module.exports = echo;
