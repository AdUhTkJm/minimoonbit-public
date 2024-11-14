# MiniMoonbit

这是 MiniMoonbit 挑战赛的参赛作品，实现了完整的 MiniMoonbit 编译器。

大致流程如下：

### Lexing

词法分析，处于`src/lex`下。

实现了简单的 token 切分，无需正则表达式处理。

### Parser

句法分析，处于`src/parser`下。

根据 MiniMoonbit.g4 文件，利用递归下降法解析 AST.

### KNF

中间语言转换，将 AST 转变为 K-Normal Form (KNF).

在 KNF 上作出了少量优化：
- 常量折叠
- 尾递归的辨别
- 无用代码删除

尾递归向循环的转化在 RISC-V 阶段进行。

### Closure

将 KNF 转化为 Closure IR，在合适的地方标记闭包的封装与调用。

在 Closure IR 上作出了少量优化：
- 公共子表达式消除 (CSE)
- 无用代码删除

计划将所有不会逃逸自身所在环境的闭包转化为普通函数，对应的转化功能现在还有错误。

### RISC-V

目标代码生成。

这实际上集成了两个阶段：将 Closure IR 转化为 3-address IR，然后进行寄存器分配。

在 3-address IR 上作出了少量优化：
- 循环不变量提取

在最终生成的汇编上进行了大量整理工作，以减少最终的指令数目。