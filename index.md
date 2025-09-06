---
title: Learning Rust
---



###  01 初见Rust

##### Rust工具链

```
rustup update stable
rustup self uninstall
rustup doc //打开本地文档
```

```
cargo new hello
cargo run //先调用了cargo build
cargo clean //清除存在的编译结果
cargo build //默认debug
cargo build --release
cargo check //检查语法错误
```

```
rustc main.rs
./main
```

##### 宏

```rust
fn main() {
    println!("Hello, world!");
}
```

##### 函数

```rust
fn gcd(mut x: u64, mut y: u64) -> u64 {
    assert!(x != 0 && y != 0);
    while y != 0 {
        if x > y {
            let t = x; //类型推断（let t: u64 = x）
            x = y;
            y = t;
        }
        y %= x;
    }
    x
}
```

##### 测试函数

- 仅用于测试，正常情况无需编译

```rust
#[test] //称为attribute
fn test_gcd() {
    assert_eq!(gcd(14, 15), 1);
}
```

```
cargo test
```

##### 命令行参数

```rust
use std::env;
use std::str::FromStr;

fn main() {
    let mut a = Vec::new();
    for arg in env::args().skip(1) { //获得参数，忽略第一个
        a.push(u64::from_str(&arg).expect("error parsing argument"));
    }

    if a.len() == 0 {
        eprintln!("Usage: gcd NUMBER ..."); //写入标准错误
        std::process::exit(1);
    }

    let mut d = a[0];
    for i in &a[1..] {
        d = gcd(d, *i);
    }
	
    println!("{:?} 的最大公约数是 {}", a, d);
}
```

- std：a crate
- env：a module in std
- FromStr：a trait in std::str

```rust
pub trait FromStr {
    type Err;
    fn from_str(s: &str) -> Result<Self, Self::Err>;
}
```

- Vec：a struct in std::vec；re-exported by std::prelude
- new：a method in Vec

##### Rust语言之怪现象

- 变量缺省不可被修改，但总可以被覆盖

```rust
let x = 5;
let x = x + 1;
{
    let x = x * 2;
    //x = 12
}
//x = 6
```

- 代码块具有值

```rust
let y = {
    let z = x * x;
    z / 2
}
```

### 02 基础类型

##### 整数类型

- 无符号整数：u8，u16，u32，u64，u128，usize（内存地址宽度）
- 有符号整数：i8，i16，i32，i64，i128，isize（内存地址宽度）

```rust
123u8, -1680isize
0x0fffffi32, -0o1670isize, 0b1100u8
0x_0f_ffff_i32, -0o_1_670_isize
```

- 推断出多种可能类型，如果i32是其中一种则为i32，否则编译器报错

- ASCII字符字面量

```rust
b'A' //=65u8
b'\x41' //=65u8
b'\'', b'\\', b'\n'
```

- as类型转换

```rust
assert_eq!(1000_i16 as u8, 232_u8);
assert_eq!(-10_i8 as u16, 65526_u16); //符号位高位填补
```

- 附着方法

```rust
2_u16.pow(4)
u16::pow(2, 4)

(-4_i32).abs()
i32::abs(-4)

0b1001_u8.count_ones()
u8::count_ones(0b1001)
```

- 函数调用优先级高于一元前缀操作符优先级

```rust
assert_eq!((-4_i32).abs(), 4);
assert_eq!(-4_i32.abs(), -4);
```

##### 整数运算溢出

```rust
let mut num = 1;
loop {
    num *= 2;
}
//debug模式下panic
```

- checked operations

```rust
loop {
    num = num.checked_mul(2).expect("overflowed");
}
//dubug和release模式下
```

```rust
assert_eq!(10_u8.checked_add(2), Some(30));
assert_eq!((-128_i8).checked_div(-1), None);
//None.expect("xxx")：导致panic，输出xxx
//Some(num).expect("xxx")：返回num
```

- wrapping operations

  与release模式下的缺省溢出行为完全相同

```rust
assert_eq!(500_u16.wrapping_mul(500), 53392);
```

- overflowing operations

  wrapping operation下的计算结果

```rust
assert_eq!(255_u8.overflowing_sub(2), (253, false));
assert_eq!(5_u16.overflowing_shl(17), (10, true)); //17 % 16 = 1
```

- saturating operations

  类型表示范围内距离结果最近的值

  除、取余、位移没有saturating operations

```rust
assert_eq!(32760_i16.saturating_add(10), 32767);
```

##### 浮点数类型

- f32、f64
- 无法推断则默认为f64

```rust
31415.926e-4f64
f64::MAX
f64::MIN
f64::INFINITY
f64::NEG_INFINITY
f64::NAN
```

```rust
println!("{}", f64::NAN == f64::NAN); //false
println!("{}", f64::is_nan(f64::NAN)); //true
```

```rust
let a = 0.0 / 0.0; //NAN
let b = f64::sqrt(-1.0); //NAN 
```

- 常量

```rust
use std::f64::consts::PI;

println!("{}", PI);
println!("{:/20}", PI); //20位，不够则补0
```

##### 工具函数size_of

```rust
use std::mem;
println!("{}", std::mem::size_of::<isize>());
```

##### 布尔类型

- 1字节
- as操作符可将bool转为整数，无法将数字转为bool

```rust
assert_eq!(false as i32, 0);
assert_eq!(true as f32, 1); //error
assert_eq!(1 as bool, true); //error
```

##### 字符类型

- 4字节

- 字面量

```rust
'\xHH' //ASCII
'\u{HHHHHH}' //Unicode
```

- char转换为整数

```rust
assert_eq!('👍' as u32, 0x1f44d);
```

- u8转换为char

```rust
assert_eq!(97_u8 as char, 'a');
assert_eq!(97_u16 as char, 'a'); //error
```

- u32转换为char

```rust
use std::char
assert_eq!(char::from_u32(0x2764), Some(❤));
assert_eq!(char::from_u32(0x110000), None);
```

##### 元组类型

```rust
let t = (1, false, 0.1); //类型推断
let t1: (i64, bool, f32) = (t.1, t.2, t.3);

println!("{:?}", t);

let i: usize = 1;
pritln!("{}", t[i]); //error
```

```rust
let t = (1, false, ); //最后一个值后可添加逗号

let t1: (i32, ) = (1 + 1, ); //1元组最后必须添加逗号

let t0: () = (); //0元组不能出现逗号
```

- 作为函数返回值

```rust
fn f(x: i32, y: i32) -> (i32, i32) {}

let (x, y) = f(1, 2);
```

```rust
fn f(x : i32) {} //实际返回0-tuple
```

##### 指针类型

- 引用（Reference）

```rust
let v: i32 = 123;
let r = &v;
let r1: &i32 = &v;

let v1: i32 = *r; //去引用（dereference）
*r = 456; //error，只读

println!("{:p}", r); //地址
println!("{}", r); //123
```

```rust
let r = &v;
let r_e = &v;
assert!(ptr_eq(r, r_e));
assert!(!ptr_eq(r, r_e));
```

```rust
let mut v: i32 = 123;
let r = &mut v;
*r = 456;
```

- Box

  值存在堆中

```rust
let v = 123;
let b = Box::new(v);
let mut b1: Box<i32> = Box::new(v);
*b1 = 456;
```

- raw pointer

```rust
let mut x = 10;
let ptr_x = &mut x as *mut i32;
let y = Box::new(20);
let ptr_y = &*y as *const i32;

unsafe {
    *ptr_x += *ptr_y;
}
```

##### 数组、向量、切片

- array 数组

  缺省被放置在栈中

```rust
let a: [u32; 5] = [0, 1, 2, 3, 4];
let b = [true, false, true];
let c = [0; 100];
```

- vector 向量

  自身在栈中，元素在堆中

```rust
let v: Vec<i32> = vec![];
let v = vec![1, 2, 3];
let v = vec![0; 10];
v.insert(3, 10);
v.remove(1);
```

```rust
let mut vec: Vec<u16> = Vec::with_capacity(10);
for i in 0..10 {
    vec.push(i);
}
vec.push(10); 
assert!(vec.capacity() >= 11); //内存重分配
```

```rust
let mut v = vec![];
v.push(1);
assert_eq!(v.pop(), Some(1));
assert_eq!(v.pop(), None);
```

- slice 切片

```rust
let mut a = [0, 1, 2, 3];
let s = &a[0..2]; //[0, 2)

let s = &a; //不是切片
let s: &[u16] = &a; //是切片
let s = &a[..];
let s = &a[1..];
let s = &a[..3];
```

```rust
fn f(s: &[u16]) {}

let a = [0, 1, 2];
let v = vec![0, 1, 2];
f(&a);
f(&v);
```

```rust
//slice上附着的所有方法都适用于array和vector
v.sort();
v.reverse();
```

##### 字符串类型

```rust
fn main() {
    let s = "\"hello world\"";
    
    let s = "hello
    world"; //包含每一行前面空格
    
    let s = "hello\
    world"; //一行
    
    let s = r"\"; //停止转义操作，无法放置"字符
    let s = r##"\"##; //可以放置"字符
}
```

- 内存中采用UTF-8编码，不同字符编码长度可能不同
- 两种类型字符串：String（特殊的Vec\<u8>）、&str（特殊的&[u8]）

```rust
let v = "hello".to_string();
let v = String::from("world");

let s = &v[1..4];
let l = "hello world"; //类型&str，所引用字符串在内存的只读区域中
```

```rust
let s = format!("hello {}", "world");
let s = format!("x = {x}", x = 1);
```

```rust
assert_eq!(["hello", "world"].concat(), "helloworld");
assert_eq!([[1, 2], [3, 4]].concat(), [1, 2, 3, 4]);
assert_eq!(["hello", "world"].join(" "), "hello world");
assert_eq!([[1, 2], [3, 4]].join(&0), [1, 2, 0, 3, 4]);
assert_eq!([[1, 2], [3, 4]].join(&[0, 0][..]), [1, 2, 0, 0, 3, 4]);
```

```rust
assert_eq!("中文".len, 6);
assert_eq!("中文".chars().count(), 2);
assert_eq!("English".len(), 7);
assert_eq!("English".chars().count(), 7);
```

- mutable String

```rust
let mut s = String::from("hello");
s.push(' ');
s.push_str("world");
s.insert(5, ' ');
s.insert_str(11, "!!");
```

```rust
let mut s = String::from("中文")；
s.push('串')；
s.insert(1, 'E'); //error
```

```rust
let mut z = String::from("English");
z[0] = 'e'; //error
```

- mutable &str

```rust
let mut z = String::from("English");
let s = &mut z[0..3];
println!("{}", s.make_ascii_lowercase());
```

- 比较操作符

```rust
let a = "Dog".to_lowecase() == "dog"; //true
let a = "Dog" != "dog"; //true
let a = "Dog" > "dog"; //false
```

```rust
let s0 = "th\u{e9}"; //thé
let s1 = "the\u{301}"; //thé
println!("{}", s0 == s1); //false
```

- 其他常用方法

  当在String上调用&str上的方法时编译器会自动把String转换为&str

```rust
println!("{}", "Hello, world!".contains("world")); //true
println!("{}", "Hello, world!".replace("world", "dog")); //Hello, dog!
println!("{}", " Hello  \n  ".trim() = "Hello"); //true

for word in "Hello world and dog".split("") {
    println!("{}", word);
}
```

- Byte String

  本质是[u8; N]

  String literal的各种语法都适用于Byte String（Raw Byte String的前缀的br）

  String和&str上的方法不适用于Byte String

```rust
let s = b"GET";
assert_eq!(s, &[b'G', b'E', b'T']);
```

##### 类型别名

```rust
type Bytes = Vec<u8>;
let a: Bytes = vec![0, 1, 2];
```

##### 用户自定义类型

- struct

```rust
struct Image {
    size: (usize, usize),
    pixels: Vec<u32>
}
impl Image {
    //type-associated function
    fn new(w: usize, h: usize) -> Image {
        Image {
            pixels: vec![0; w * h];
            size: (w, h);
        }
    }
    //value-associated function
    fn sizes(&self) -> (usize, usize) {
        self.size
    }
}

let image = Image {
    pixels: vec![0; width * height],
    size: (width, height)
};
```

- enum

```rust
#[derive(PartialEq)]
enum Ordering {
    Less,
    Equal,
    Greater
}
fn cmp(a: i32, b: i32) -> Ordering {
    if a < b {
        Ordering::Less
    } 
    else if a > b {
        Ordering::Greater
    } 
    else {
        Ordering::Equal
    }
}
impl Ordering {
    fn is_eq(self) -> bool {
        if self == Ordering::Equal {
            true
        } 
        else {
            false
        }
    }
}
```

```rust
#[derive(PartialEq)]
enum Color {
    RGB(u8, u8, u8),
    Gray(u8)
}
impl Color {
    fn is_gray(&self) -> bool {
        match self {
            Color::Gray(_) => true,
            Color::RGB(a, b, c) =>
            	if a == b && b == c {
                    true
            	} 
            	else {
                	false    
            	}
        }
    }
}
```

```rust
//std::option::Option
pub enum Option<T> {
    None,
    Some(T),
}
fn divide(x: f64, y: f64) -> Option<f64> {
    if y == 0.0 {
        None
    } 
    else {
        Some(x / y)
    }
}
```

##### Rust关于Memory的若干基本概念

- Value

  Type + Byte Representation

  Independent of where the value is stored

- Place

  A location in memory that can hold a value

  can be on stack, the heap, …

- Variable

  A place on the stack

  a named value slot on the stack

- Pointer

  A value that holds the address of a place

  That is, a pointer points to a place

```rust
let x = 5;
let v = &x;
//Value: 5k, &x
//Place: x, v
//Variable: x, v
//Pointer: &x

//let x = vec![0, 1, 2];
//let y = &x[1..3];
```



### 03 所有权与所有权转移

##### 示例

- C++

```cpp
std::string *ptr;
{
    std::string s = "Hello world";
    ptr = &s;
}
//无法访问变量s
std::cout << *ptr; //可以访问到s原本空间
```

- Rust

```rust
let ptr: &String;
{
    let s = String::from("Hello world");
    ptr = &s; //error
}
//无法访问变量s
println!("{}", ptr);
```

##### Rust中的所有权

- 在任意时刻

  1、一个值具有唯一一个所有者

  2、每一个变量，作为根节点，出现在一棵所有权关系树中

  3、当一个变量离开当前作用域后，它所有权关系树中的所有值都无法再被访问，其中所有存在堆中的值所占空间会被自动释放

- 扩展/软化措施

  1、所有权转移

  2、简单变量豁免

  3、引用计数指针类型

  4、borrow a ref to a value

##### 所有权转移

- 对no-copy type的值，发生如下操作时

  1、赋给一个变量

  2、作为参数传入函数调用

  3、在函数调用中返回

```rust
let s = vec![1, 2, 3];
let t = s; //s栈空间的值拷贝到t的栈空间
let u = s; //error
```

- Python：赋值成本低（增加引用计数），内存管理成本高（运行时垃圾回收、循环引用难处理）

  C++：赋值成本高（深层复制），内存管理成本低

  Rust：赋值成本低（近拷贝栈空间），内存管理成本低

```rust
let s = vec![1, 2, 3];
let t = s.clone(); //实现C++赋值行为
```

```rust
let mut s = String::from("abc");
s = String::from("def"); //原来堆空间释放
```

- 条件语句

  若变量有可能在某一个分支被剥夺所有权，即使运行没经过该分支也不能读该变量

```rust
let x = vec![1, 2, 3];
let c = 1;
if c < 0 {
    f(x);
} 
println!("{:?}", x); //error
```

- 循环语句

```rust
let x = vec![1, 2, 3];
let mut len = x.len();
while len > 0 {
    f(x); //error
    len -= 1;
}
```

```rust
let mut x = vec![1, 2, 3];
let mut len = x.len();
while len > 0 {
    f(x);
    x = vec![1, 2, 3];
    len -= 1;
}
```

- 数组、向量、切片

  不允许仅通过赋值把某位置上元素的所有权转移

  多数情况不必转移所有权，取得元素的引用可能就足够

```rust
let mut v = vec![String::from("abc"), String::from("def"), String::from("ghi"), String::from("jkl")];
let x = v[1]; //error
```

```rust
//从向量中，成本高
let e = v.remove(1);
println!("{:?}", v); //["abc", "ghi", "jkl"]
```

```rust
//从向量中
let e = v.swap_remove(1);
println!("{:?}", v); //["abc", "jkl", "ghi"]
```

```rust
//从向量中
let e = v.pop().expect("empty");
println!("{:?}", v); //["abc", "def", "ghi"]
```

```rust
//从向量/数组/切片中
let e = std::mem::replace(&mut v[1], String::from("dog"));
println!("{:?}", v); //["abc", "dog", "ghi", "jkl"]
```

```rust
//必须是具有缺省值的类型
let e = std::mem::take(&mut v[1]);
println!("{:?}", v); //["abc", "", "ghi", "jkl"];
```

```rust
//显示标注是否有值
let mut v = vec![Some(String::from("abc")), Some(String::from("def"))];
let e = std::mem::take(&mut v[1]);
println!("{:?}", v); //[Some("abc"), None]
println!("{:?}", e); //Some("def")
```

- 向量/数组的所有权转移给循环语句

```rust
for s in v {
    println!("{}", s);
    //不能读取v
}
//不能读取v
```

##### Copy Types

- 语言自带的所有数字类型（整数、浮点数），char/bool，若干其他类型，元素类型为Copy Type的数组，所有元素类型均为Copy Type的元组
- 用户自定义的数据类型缺省情况下都不是Copy Type

```rust
let n1 = 5;
let n2 = n1; //栈中新的空间
```

- Copy Types与自定义数据类型

  如果struct类型包含的所有分量类型都是Copy Type，那么可以通过attribute将该类型声明为Copy Type

```rust
struct C { x: u32 }
let l = C { x: 3 };
f(l);
println!("{}", l.x); //error
```

```rust
#[derive(Copy, Clone)]
struct C { x: u32 }
let l = C { x: 3 };
f(l);
println!("{}". l.x); //3
```

```rust
#[derive(Copy, Clone)]
struct C { x: u32, s: String }
let l = C { x: 3, s: String::from("dog") }; //error
f(l);
println!("{}". l.x);
```

##### 共享所有权

```rust
use std::rc::Rc;

//可以不必写类型声明
let s: Rc<String> = Rc::new(String::from("dog"));
let t: Rc<String> = s.clone(); //Method-call syntax
let u: Rc<String> = Rc::clone(&s); //Fully qualified syntax

//可以在Rc<T>类型的值上直接调用T类型的值上的方法

println!("{}", RC::strong_count(&s)); //3

let t = 0;
let u = 1;

println!("{}", RC::strong_count(&s)); //3
```

- 被Rc拥有的值不可修改

```rust
let s = Rc::new(String::from("dog"));
s.push_str("!"); //error
```

- Rc：non-thread-safe，速度快

  Arc：thread-safe，速度慢

- 使用建议：始终用Rc，除非编译器告诉用Arc（多线程环境下使用Rc会被编译器检查出来）

### 04 引用

##### 引用

- 共享型引用（shared reference）

  只能读取，不能修改，从该值出发可以访问到的任何东西都不能被改变

  任一时刻一个值可有任意多个

  只要存在共享引用，所有者也不能修改

- 可变型引用（mutable reference)

  读取、修改均可

  任一时刻最多只能有一个可变引用，此刻不能再有只读引用

  只要存在可变引用，所有者无法访问

```rust
let x = 10;
let r = &x;
```

```rust
let mut x = 10;
let m = &mut x;
*m = 20;
```

- 操作符左侧的引用/非引用

```rust
struct C {x: i32}
let c = C {x: 5};
let r = &c;
println!("{}", (*r).x);
println!("{}", r.x); //自动dereference，完全等价
```

```rust
let mut v = vec![3, 1, 2];
(&mut v).sort();
v.sort(); //自动reference，完全等价
```

- 对引用的赋值

```rust
let x = 10;
let y = 20;
let mut r = &x;
println!("{}", r); //10
r = &y;
println!("{}", r); //20
```

```cpp
int x = 10;
int y = 20;
int &r = x;
cout << r; //10
r = y;
y = 30;
cout << r; //20
cout << x; //20
cout << y; //30
//C++引用在创建后不能再引用另外的值
```

- 引用的引用

```rust
struct C {x: i32}
let c = C {x: 5}
let r = &c;
let rr = &r;
let rrr = &rr;
println!("{}", rrr.x); //5
```

- 引用的比较

```rust
let x = 10;
let y = 10;
let rx = &x;
let ry = &y;
let rrx = &rx;
let rry = &ry;
println!("{}", rrx == rry); //true，看穿任意层数的引用
println!("{}", rrx < ry); //error，类型必须相同

println!("{:p}", rx); //x的地址
println!("{}", std::ptr::eq(rx, ry)); //false
```

- 空引用

```rust
let x = 10;
let r = Some(&x); //Option<&i32>
let null = None;
println!("{}", r == null); //false
let r = r.expect("空指针");
println!("{}", r);
```

- 在任意表达式上创建引用

```rust
fn fac(n: usize) -> usize {
    (1..n+1).product()
}
let r = &fac(5);
println!("{}", r + &1); //121，看穿一层引用
```

- 对slice的引用

  类型&[T]，一种fat pointer，包含首元素地址、元素数量

##### 引用的安全性

- 在局部变量上创建引用

```rust
let r;
{
    let x = 1;
    r = &x;
}
println!("{}", r); //error
```

- Lifetime

  约束1：&x的lifetime不能超过x的lifetime

  约束2：&x赋给变量r，&x的lifetime不能小于语句r=&x到r的lifetime终止处

```rust
let x = 1;
{
    let r = &x;
    println!("{}", r);
}
```

```rust
let v = vec![1, 2, 3];
let r = &v[1];
//v[1] >= &v[1] >= r
```

```rust
let x = 1;
let y = 2;
let rv = vec![&x, &y];
//x >= &x >= rv
//y >= &y >- rv
```

- 引用作为函数参数

```rust
//全局变量lifetime与程序运行的lifetime相同
static mut S: &i32 = &0; //全局变量必须初始化
fn f<'a>(p: &'a i32) {
    unsafe {
        S = p; //必须满足约束p >= S，但不总是满足 
    } //只能在unsafe代码块访问可变全局变量
}
```

```rust
static mut S: &i32 = &0;
fn f(p: &'static i32) {
    unsafe {
        S = p;
    }
}
```

- 调用具有引用参数的函数

```rust
static T: i32 = 1024;
f(&T);
unsafe {
    println!("{}", S);
}
```

```rust
let t: i32 = 1024;
f(&t); //error
```

- 函数返回引用

  如果函数仅有⼀个参数，且类型为引用，函数返回⼀个引用类型的值，函数的声明中不存在lifetime参数，那么默认参数与返回值具有相同的lifetime

```rust
fn f(v: &[i32]) -> &i32 {
    let mut s = &v[0];
    for r in &v[1..] {
        if r < s { s = r; }
    }
    s
}
let s;
{
    let v = [1, 2, 3];
    s = f(&v);
    println!("{}", s); //ok
}
println!("{}", s); //error
```

- struct中包含引用

```rust
struct S { r: &i32 } //error
```

```rust
struct S<'a> { r: &'a i32 }
let s;
{
    let x = 10;
    s = S { r: &x };
}
println!("{}", s.r); //error
```

```rust
struct D { s: S<'static> } //D.s.r只能存放static reference
struct D<'a> { s: S<'a> }
```

- 不同的lifetimes

```rust
struct S<'a> { 
	x: &'a i32,
    y: &'a i32
}
let x = 10;
let r;
{
    let y = 20;
    {
        let s = S { x: &x, y: &y};
        r = s.x
    }
}
println!("{}", r);
//s.x = s.y
//s.x >= r
//y >= s.y
//y < r
//不应该限制s.x == s.y
```

```rust
struct S<'a, 'b> { 
	x: &'a i32,
    y: &'b i32
}
```

- 省略函数签名中引用的lifetime参数

```rust
//最简单情况下，为每一个引用声明独立的lifetime参数
struct S<'a, 'b> {}
fn f<'a, 'b, 'c>(r: &'a i32, s: S<'b, 'c>) -> i32 {}
```

```rust
//所有参数仅涉及一个lifetime，认为参数和返回值涉及的lifetime相同
fn f<'a>(p: &'a [i32; 3]) -> (&'a i32, &'a i32) {}
```

```rust
//附着在struct上的方法，具有参数&self，返回值涉及的lifetime和self相同
fn f<'a, 'b>(&'a self, p: &'b str) -> Option<&'a String> {}
```

##### 共享与可变

- 悬空指针

```rust
let v = vec![1, 2, 3];
let r = &v;
let u = v; //error，所有权转移
println!("{}", r[0]);

//共享型指针的lifetime内，被指针引用的不可变，不能发生所有权转移
```

```rust
fn f(vec: &mut Vec<i32>, slice: &[i32]) {}

let mut v = vec![1, 2, 3];
f(&mut v, &v); //error，已存在可变引用
```

- 共享型：子树不可改变，到根路径不可改变

  可变型：子树被引用独占，到根路径不可被访问

```rust
let mut w = (1, 2);
let r = &w;
let r0 = &r.0; //ok
let m1 = &mut r.1; //error
println!("{}", r0);
```

```rust
let mut w = (1, 2);
let m = &mut w;
let m0 = &mut m.0; //ok
*m0 = 3;
let r1 = &m.1; //ok
w.1; //error
println!("{}", r1);
```

- C中的pointer to const

```c++
int x = 1;
const int *p = &x;
x++;
cout << p; //2
```

```rust
let mut x = 1;
let p = &x;
x += 1; //error
```

##### 经过反思形成的一些信息

- 所有权不包含可变性

```rust
let s = String::from("hello");
let mut s_m = s;
s_m.push_str(" world");
```

```rust
let s = String::from("hello");
fn f(mut s_m: String) {}
f(s);
```

- C中四种形式的pointer

```c++
//pointer
int *p = &x;
*p = 3;
p = &y;
```

```c++
//pointer to const
const int *p = &x;
*p = 3; //error
p = &y;
```

```rust
//const pointer
int * const p = &x;
*p = 3; 
p = &y; //error
```

```rust
//const pointer to const
const int * const p = &x;
*p = 3; //error
p = &y; //error
```

- Rust中四种引用

```rust
let p: &i32 = &a; //const pointer to const
let p: &mut i32 = &mut a; //const pointer
let mut p: &i32 = &a; //pointer to const
let mut p: &mut i32 = &a; //pointer
```

- Rust中Box类型pointer不具有四种形式

  Box类型的pointer对所指的值有所有权，堆中值依附于栈中值

```rust
let mut a Box::new(0);
*a = 1; //ok
a = Box::new(2); //ok

let a = Box::new(0);
*a = 1; //error
a = Box::new(2); //error
```

- 限定栈值不变，堆值可变

```rust
let p = &mut 0;
*p = 1;
```

```rust
let p = &mut String::from("hello");
p.push_str(" world");
```

```rust
let p = &mut *Box::new(0);
*p = 1;
```

- shadow

```rust
let s = 1;
let r = &s;
let s = 2; //ok
println!("{}", r); //1
```

- 引用常数/表达式

```rust
let r;
{
	let x = 1;
    r = &0; //0存放在静态数据区
}
println!("{}", r);
```

```rust
let r = &fac(6); //栈中
r = &fac(6); //error
```

### 05 表达式

##### 代码块

```rust
let a = {
    println!("hello");
    1 + 2;
};
println!("{:?}", a); //()
```

```rust
let a = {
    println!("hello");
    1 + 2 
};
println!("{:?}", a); //3
```

##### 分支表达式

- let declaration

```rust
let b;
println!("{}", b); //error
if a > 0 {
    b = true;
} 
else {
	b = false;
}
```

- if-else expr

```rust
let b = if a > 0 {
    true
} 
else {
    false
};
```

```rust
let b = if a > 0 {
    true
} 
else {
    0 //error
};
```

```rust 
let b = if a > 0 {
    println!("hello");
}; //编译器添加else分支，值为()
```

- match expression

```rust
match code {
    0 => println!("0"),
    _ => println!("1"),
}
```

```rust
let name = match a {
    Some(v) => v,
    None => String::from("None")
};
```

- if let expr

```rust
if let Some(v) = a {} 
else {}
```

##### 循环表达式

- while循环表达式

```rust
'outer:
while a <= x {
    while b <= x {
        if a * b == x {
            break 'outer; //跳出嵌套循环
        }
        b += 1;
    }
    a += 1;
    b = 1;
}
```

- while-let循环表达式

```rust
let a = [Some("a"), Some("b"), None, Some("c")];
while let Some(s) = a[i] {
    i += 1;
    if i == a.len() {
        break;
    }
}
```

- for循环表达式

```rust
for e in a {
    if let Some(s) = e {
        i += 1;
    }
    else {
        break;
    }
}
```

```rust
for i in 1..=100 {}
for i in 1..101 {}
```

- loop循环表达式

```rust
let sqrt = 'outer: loop {
    n += 1;
    for i in 1.. {
        let sqr = i * i;
        if sqr == n {
            break 'outer i; //break后放一个值
        }
        if sqr > n {
            break;
        }
    }
};
```

##### return expr

- 终止函数，返回表达式的值

##### 运算

```rust
println!("{}", -100u32); //error，-不能作用在无符号整数上
println!("{}", +100); //error，不存在意愿操作符+
println!("{}", 123.4 % 10.0); //%适用于浮点数
println!("{}", !0x10); //按位取反是!
```

- 位运算优先级高于比较运算
- 比较运算符两个操作数类型必须相同
- 带有短路行为的逻辑运算操作符两个操作数类型必须为bool

##### 赋值

- 右侧non-copy type发生所有权转移
- 支持复合赋值操作符：+=
- 不支持自增自减：++、--
- 不支持链式赋值：a = b = 1

##### 类型转换

- 内置数字类型间都可相互转换，浮点转换到整数向0取整
- bool、char、类C的enum类型可转换为任何整数类型
- 一些unsafe pointer type之间也可转换
- 隐式转换：&mut T→T、&String→&str、&Vec\<T\>→&[T]、&Box\<T\>→&T

### 06 错误处理

##### 程序内部错误

- 应对方式：panic
- 程序检测到某种错误即将发生；程序在执行中调用了宏panic!
- unwinding（缺省行为）：打印错误信息、逆序释放、退出线程，不影响其他线程
- aborting：unwinding过程中对某个值的drop方法调用又产生了panic；使用编译参数-C panic=abort

##### 程序外部错误

- 应对方式：the Result type

```rust
enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

- Result<T, E>上方法

  除is_ok和is_err都会所有权转移

```rust
rst.is_ok() //Ok(T)返回true，Err(E)返回false
rst.is_err() //!rst.is_ok()
rst.ok() //返回Option<T>
rst.err() //返回Option<E>
rst.unwrap() //Ok(T)返回T，否则panic
rst.expect(msg) //与rst.unwrap()相同，触发panic后打印msg
rst.unwrap_or(fallback) //Ok(T)返回T，否则返回fallback
rst.unwrap_or_else(fallback_fn) //Ok(T)返回T，否则返回fallback_fn()的返回值
```

```rust
rst.as_ref() //转为Result<&T, &E>
rst.as_mut() //转为Result<&mut T, &mut E>
```

```rust
if rst.is_ok() {
    println!("{}", rst.unwrap());
}
else {
    println!("{}", rst.err().unwrap()); //unwrap也适用于Option<T>
}
```

- Result<T, E>的别名

```rust
pub type Result<T> = Result<T, Error>;
```

- 标准库中定义的Error

```rust
std::io::Error
std::fmt::Error
std::str::Utf8Error
//核心是std::error::Error
```

```rust
println!("{}", err); //简要信息
println!("{:?}", err); //详细信息
err.to_string()
err.source() //返回Option<E>，表示错误发生的源错误，不存在则None
```

- 错误的传播

  所在的函数返回值类型为Result<T, E>，且err类型为E

```rust
let v = match f() {
    Ok(suc) => suc,
    Err(err) => return Err(err)
};
```

```rust
let v = f()?;
```

### 07 Crates and Modules

##### Crate

- 由module构成的树
- Library crate编译后得到库文件，Binary crate编译后得到可执行程序
- crate root：对crate进行编译的起点

```
cargo new //创建的项目缺省仅包含一个binary crate
cargo build --verbose //编译过程细节
```

- 同时包含main.rs和lib.rs

```rust
let c = crate_main_lib::add(1, 2);
```

```rust
use crate_main_lib::add;
let c = add(1, 2);
```

```rust
use crate_main_lib::add as plus;
let c = plus(1, 2);
```

- 一个lib crate关联多个binary crates

  ./src/bin下的每一个rs文件是一个binary crate的root

```
cargo run --bin file_name
```

- 两个本地crates之间建立依赖关系

```toml
[dependencies]
calc = { path = "../calc" }
```

```rust
use calc::add;
```

##### module

- a collection of items

- items：function、type、module、constant……

- 可见性

  private：当前及后代模块内

  pub(crate)：当前crate内

  pub：当前模块内外

  pub(super)：父模块及后代模块内

  pub(in \<path\>)：一个祖先模块及后代模块内（只能指向当前item所在模块或其祖先模块）

```rust
pub mod arith {
    pub mod simple {
        pub fn add(a: i32, b: i32) -> i32 { a + b }
    }
}
```

- 当前：self；父：super；根：crate

```rust
super::simple::add
crate::arith::simple::add
arith::simple::add //当前
self::arith::simple::add //永远指向亲兄弟
::arith::simple::add //外部crate
```

- use语句

```rust
add(1, 2); //ok
use self::arith::simple::add;
add(1, 2); //ok
{
    add(1, 2); //ok
    mod inner {
        pub fn f() -> i32 {
            add(1, 2) //error，代码块中定义的模块无法使用use引入的别名
        }
    }
}
```

```rust
pub mod a {
    pub fn f() -> i32 {
        super::b::add(1, 2);
        crate::b::add(1, 2);
        crate::add(1, 2);
    }
}
add(1, 2); //ok
use self::b::add;
pub mod b {
    pub fn add() {}
}
```

- 一条use语句引入多个items

```rust
use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::io::prelude::*; //所有可见的items
```

- pub use

```rust
pub mod a {
    pub mod b {
        pub fn add() {}
        pub(crate) fn add() {} //error，re-exporting不能与item可见性冲突
    }
    pub use self::b::add; //re-exports the item add
    pub fn f() -> i32 { add(1, 2) }
}
pub fn f() -> i32 { self::a::add(1, 2) }
```

- 一个crate放在多个文件中

  四种存放方式：embed、single file、file+dir、dir

```rust
// main.rs
fn main() {}
mod calc;
```

```rust
// ./calc.rs ./calc/mod.rs
pub mod arith;
```

```rust
// ./calc/arith.rs ./calc/arith/mod.rs
pub mod simple;
```

- 预先imports的items：std、std::prelude::*
- 控制Struct中Field的可见性

```rust
pub mod a {
    pub mod b {
        pub struct C {
            pub x: i32,
            pub(super) y: i32,
            z: i32
        }
        //x, y, z
    }
    //x, y
}
// x
```

- 在模块中定义static和constant items

  const：类似#define定义的宏常量，不存在mut

  static：一种变量，生存期与程序相同，存在mut（mut static不具有线程安全性，只能在unsafe中使用）

```rust
pub mod a {
    pub const C: f64 = 1.0;
    pub static F: f64 = 2.0;
}
```

- 在item上声明attributes

```rust
mod a {
    //#[warn(dead_code)]
    fn f() {}
    #[allow(dead_code)]
    fn f() {}
}
```

```rust
#[cfg(...)]
```

```rust
#[inline]
#[inline(always)]
#[inline(never)]
```

```rust
#![allow(dead_code)] //作用到所有后代模块的所有相关程序元素
```

```rust
#[test]
#[inline] //不能#![]
#![feature(...)] //只能#![]
```

##### 添加单元测试代码

```
cargo new unit_test --lib
cargo test
```

```rust
#[cfg(test)] //只在测试时编译
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
```

- 常用的两个宏

  在非测试代码中可以使用，会被编译到release中，带debug前缀只在debug有效

```rust
assert!();
assert_eq!();
```

- 测试一定会panic

```rust
#[test]
#[should_panic(expected="divide by zero")]
fn f() {
    let a = if 2 > 3 {1} else {1};
    let b = if a > 0 {0} else {0};
    let c = a / b;
}
```

- 返回Result<(), E>

```rust
#[test]
fn f() -> Result<(), ParseIntError> {
    i32::from_str_radix("a11", 10)?;
    Ok(())
}
```

- 选择测试函数

```
cargo test f //选择存在该字符串的所有测试函数
```

##### 添加集成测试代码

- 放在./tests/目录下，每一个rs文件视为一个crate

```rust
// ./tests/test_1.rs
use inte_test::calc::add;
```

##### 添加说明文字

```rust
#![doc = "hello"]

#[doc = "hello"]
pub mod a {}
```

```
cargo doc --no-deps --open
```

- doc attr的语法糖

```rust
/// hello
//! hello
```

- 在doc添加代码块

```rust
/// code
///
/// 	println!("hello");
/// 	
```

```rust
/// code
/// '''
/// println!("hello");
/// '''
```

- 指定代码行不出现在doc文档

```rust
/// code
/// '''
/// # println!("hello");
/// '''
```

- doc中代码块被编译为测试函数

```rust
/// code
/// '''ignore //不编译运行
/// println!("hello");
/// '''
```

```rust
/// code
/// '''no_run //编译，不运行
/// println!("hello");
/// '''
```

##### 在cargo项目中声明外部依赖

- 外部crate放在本地项目中

```toml
[dependencies]
util = { path = "util" }
```

```toml
[dependencies]
calc = { path = "../calc" }
```

- 外部crate放在远程git仓库中

```toml
[dependencies]
regex = { git = "https://github.com/rust-lang/regex" }
```

```toml
[dependencies]
regex = { git = "https://github.com/rust-lang/regex", branch = "next"}
```

- 外部crate放在crates.io上

```toml
[dependencies]
image = "0.13.0" //考虑多方需求，找到与0.13.0兼容的尽可能新的版本
```

##### 版本号管理

- Major.Minor.Patch

  Major/主版本号：不具兼容性改变

  Minor/次版本号：具有兼容性的增强

  Patch/修订号：修复

- 兼容性判断

  两个0.0前缀不存在兼容关系

  两个相同0.x（x非0）存在兼容关系

  主版本号相同具有兼容关系

- Caret requirements

  ^0：[0.0.0, 1.0.0)，不兼容

  ^0.0：[0.0.0, 0.1.0)，不兼容

  ^0.0.3：[0.0.3, 0.0.4)，不适用

  ^0.2：[0.2.0, 0.3.0)，兼容

  ^0.2.3：[0.2.3, 0.3.0)，兼容

  ^1：[1.0.0, 2.0.0)，兼容

  ^1.2：[1.2.0, 2.0.0)，兼容

  ^1.2.3：[1.2.3, 2.0.0)，兼容

- Tilde requirements

  ~1：[1.0.0, 2.0.0)

  ~1.2：[1.2.0, 1.3.0)

  ~1.2.3：[1.2.3, 1.3.0)

- Other requirements

  Wildcard：\*、1.\*、1.2.\*

  Comparison：>=1.2.0、<2、=1.2.3

  Combination：>=2, < 1.5

- Cargo.lock记录当前项目直接/间接依赖的外部crates来源与真实版本，本地缓存，供所有Cargo项目复用

```
cargo update //重新计算
```

##### 把自己编写的crate发布到crates.io

```
cargo package
cargo login <key>
cargo publish
```

##### 把项目组织为workspace

- 在所有cargo项目的上层目录创建Cargo.toml文件，删除每一个carog项目中的Cargo.lock和target目录

```toml
[workspace]
members = ["crate_1", "crate_2"]
```

```
cargo build --workspace
```

### 08 结构体

##### Named-Field Struct

```rust
struct Image {
    size: (usize, usize),
    pixels: Vec<u32>
}
let im = Image {
    pixels: vec![0; w * h],
    size: (w, h)
};
```

- 一个语法糖

```rust
fn new(size: (usize, usize), pixels: Vec<u32>) -> Image {
    Image { size, pixels }
}
```

- 可见性，缺省为private

```rust
pub struct Image {
    pub size: (usize, usize),
    pub pixels: Vec<u32>
}
```

- partially moved

  其他field仍然可以正常访问，自身的所有权不能再被转移

```rust
let a = A {
    x: String::from("hello"),
    y: String::from("world"),
    n: 1
};
let s = a.x;
println!("{}", a.n); //ok
println!("{:?}", a); //error
```

- 缺省值表达式

```rust
fn f(a: A) -> (A, A) {
    let a1 = A { n: a.n + 1, ..a };
    let a2 = A { x: a1.x.clone(), y: a1.y.clone(), ..a1 };
    (a1, a2)
}
```

##### Tuple-Like Struct

```rust
struct Bound(usize, usize);
let b = Bound(1024, 768);
println!("{}, {}", b.0, b.1);
let Bound (b0, b1) = b;
```

##### Unit-Like Struct

```rust
#[derive(Debug)]
struct OneSuch;
let o = OneSuch;
println!("{:?}", o);
```

##### 通过impl代码块添加方法

- 冗余版本

```rust
pub struct Queue {}
impl Queue {
    pub fn new() -> Queue {}
    pub fn is_empty(self: &Queue) -> bool {}
    pub fn push(self: &mut Queue, c: char) {}
    pub fn pop(self: &mut Queue) -> Option<char> {}
    pub fn split(self: Queue) -> (Vec<char>, Vec<char>) {}
}

let mut q = Queue::new();
Queue::push(&mut q, 'a');
```

- 简洁版本

```rust
impl Queue {
    pub fn new() -> Self {}
    pub fn is_empty(&self) -> bool {}
    pub fn push(&mut self, c: char) {}
    pub fn pop(&mut self) -> Option<char> {}
    pub fn split(self) -> (Vec<char>, Vec<char>) {}
}

let mut q = Queue::new()
q.push('a') //dot操作符知道左边取什么形式的值
```

##### dot操作

- 用到Box

```rust
let mut bq = Box::new(Queue::new());

bq.push('a');  //从mut Box<Queue>中获得&mut Queue，获得方式&mut *bq
bq.is_empty(); //获得方式&*bq
bq.split(); //*bq发生所有权转移
```

- 用到Rc

```rust
let mut q = Queue::new();
let mut cq = Rc::new(q); //q is removed
cq.is_empty(); //获得方式&*cq
cq.push('a'); //error，被RC拥有的值is immutable
cq.split(); //error，cannot move out of an Rc
```

- Rc的两个高级函数

```rust
pub fn get_mut(this: &mut Rc<T>) -> Option<&mut T> {
    if Rc::is_unique(this) { unsafe { Some(Rc::get_mut_unchecked(this)) } } else { None }
}

let mut x = Rc::new(3);
*Rc::get_mut(&mut x).unwrap() = 4;
assert_eq!(*x, 4);
let y = Rc::clone(&x);
assert!(Rc::get_mut(&mut x).is_none());
```

```rust
pub fn try_unwrap(this: Rc<T>) -> Result<T, Rc<T>> {
    if Rc::strong_count(&this) == 1 {
        unsafe {
            let val = ptr::read(&*this);
            this.inner().dec_strong();
            let _weak = Weak { ptr: this.ptr };
            forget(this);
            Ok(val)
        }
    } else {
        Err(this)
    }
}

let x = Rc::new(3);
assert_eq!(Rc::try_unwrap(x), Ok(3));

let x = Rc::new(3);
let y = Rc::clone(&x);
assert_eq!(*Rc::try_unwrap(x).unwrap_err(), 4);
```

```rust
let mut cq = Rc::new(Queue::new());
let q = Rc::get_mut(&mut cq).unwrap(); //q is a &mut Queue
q.push('a');
q.is_empty();
let q = Rc::try_unwrap(cq).unwrap(); //cq is moved, q is a Queue
let (o, y) = q.split(); //q is moved
```

```rust
struct Node {
    tag: String,
    children: Vec<Rc<Node>>
}
impl Node {
    fn append_to(self: Rc<Self>, parent: &mut Node) {
        parent.children.push(self);
    }
}
let mut p = Node::new("p");
let mut c = Rc::new(Node::new("c"));
c.append_to(&mut p); //c的所有权转移到append_to，又被转移到向量中
```

##### 通过impl代码块添加常量

```rust
#[derive(Debug)]
pub struct Vec2D {
    x: f32,
    y: f32
}
impl Vec2D {
    const NAME: &'static str = "Vec2D";
    const UNIT: Self = Self { x: 1.0, y:0.0 };
}
println!("{}", Vec2D::NAME);
println!("{:?}", Vec2D::UNIT);
```

- 可存在多个impl代码块，必须出现在类型所在crate中

##### Generic Struct

```rust
pub struct Queue<T> {
    older: Vec<T>,
    ynger: Vec<T>
}
impl<T> Queue<T> {}
impl Queue<f64> {}
let mut q = Queue::<f64>::new();
```

##### Struct with lifetime parameters

```rust
struct Extrema<'elt> {
    min: &'elt i32, max: &'elt i32
}
fn find_extrema<'s>(slice: &'s [i32]) -> Extrema<'s> {}
```

##### Deriving Common Traits for Struct

```rust
#[derive(Copy, Clone, Debug, PartialEq)]
struct Point {}
```

- Copy：声明为copy type
- Clone：附着clone方法
- Dubug：可以通过println!("{:?}")打印
- PartialEq：可以通过相等或不等操作符判断

##### Interior Mutability

- Cell\<T\>

```rust
use std::cell::Cell;
struct S {
    regular: u8,
    special: Cell<u8>
}
let s = S {
    regular: 0,
    special: Cell::new(1)
};
s.regular = 5; //error
s.special.set(5); //ok, enables "interior mutability"
assert_eq!(s.special.get(), 5);
```

```rust
//impl<T>（定长类型T）
let c = Cell::new(1);
c.set(2);
c1.swap(&c2); //交换各自的值
let x = c.replace(5); //置换拥有的值，返回旧值
let x = c.into_inner(); //把不可变cell拆了，取出其值
```

```rust
//impl<T: Copy>（copy type T）
let x = c.get(); //复制其值
```

```rust
//impl<T: ?Sized>（任意类型T）
let mut c = Cell::new(0);
*c.get_mut() += 1; //返回可变引用

let slice: &mut [i32] = &mut [1, 2, 3];
let cell_slice: &Cell<[i32]> = Cell::from_mut(slice);
let slice_cell: &[Cell<i32>] = cell_slice.as_slice_of_cells();
```

- RefCell\<T\>

  运行时检查borrow rules是否满足

```rust
//impl<T>
let c = RefCell::new(1);
let x = c.into_inner();
c.replace(2); //panics if the value is currently borrowed
c1.swap(&d); //panics if the value in either RefCell is currently borrowed
```

```rust
//impl<T: ?Sized>
pub fn borrow(&self) -> Ref<'_, T> {}
pub fn borrow(&self) -> RefMut<'_, T> {}

let b = c.borrow();
let m = c.borrow_mut();
let b = c.borrow(); //panic
```

```rust
//impl<T: ?Sized>
let m = c.borrow_mut();
assert!(c.try_borrow().is_err());

let m = c.borrow();
assert!(c.try_borrow().is_ok());
assert!(c.try_borrow_mut().is_err());
```

- 示例

```rust
//Introducing mutability 'inside' of something immutable
let shared_map: Rc<RefCell<_>> = Rc::new(RefCell::new(HashMap::new()));
{
    let mut map: RefMut<_> = shared_map.borrow_mut();
    map.insert("a", 1);
}
let total: i32 = shared_map.borrow().values().sum();
```

```rust
//Implementation details of logically-immutable methods
struct Graph {
    edges: Vec<(i32, i32)>,
    span_tree_cache: RefCell<Option<Vec<(i32, i32)>>>,
}

impl Graph {
    fn minimum_spanning_tree(&self) -> Vec<(i32, i32)> {
        self.span_tree_cache.borrow_mut().get_or_insert_with(|| self.calc_span_tree()).clone()
    }
    fn calc_span_tree(&self) -> Vec<(i32, i32)> {
        vec![]
    }
}
```

```rust
//Mutating implementations of Clone
let s: Rc<String> = Rc::new(String::from("hello"));
let t: Rc<String> = s.clone(); //实际修改了共享的值
```

### 09 枚举

##### C-styple Enums

```rust
#[repr(i8)]
pub enum Ordering {
    Less,
    Equal,
    Greater,
}
fn compare(n: i32, m: i32) -> Ordering {
    if n < m {
        Ordering::Less
    }
    else if n > m {
        Ordering::Greater
    } 
    else {
        Equal //use std::cmp::Ordering::{self, *}
    }
}
```

- 内存中被表示为整数，类型为某个基本整数类型，缺省情况下从0开始编号

```rust
enum HttpStatus {
    Ok = 200,
    NotFound = 404,
}
assert_eq(size_of::<Ordering>(), 1);
assert_eq!(size_of::<HttpStatus>(), 2);
```

```rust
assert_eq!(HttpsStatus::Ok as i32, 200);
//as不支持将整数转换为Enum
```

```rust
fn f(n: u32) -> Option<HttpStatus> {
    match n {
		200 => Some(HttpStatus::Ok),
        ...
        _ => None,
    }
}
```

- derive traits and attach methods

```rust
impl TimeUnit {
	fn f(self) -> &'static str {
        match self {
            TimeUnit::Seconds => "seconds",
            TimeUnit::Minutes => "minutes",
        }
    }
}
```

##### Enums with Data

```rust
enum S {
    A, //Unit variant/constructor
    B(u32, u32), //Tuple variant/constructor
    C{ x: u32, y: u32 }, //Struct variant/constructor
}
```

- Enum与每一个variant以及variant的每个field具有相同可见性

##### Enum in Memory

- 包含两部分：a small integer tag to distinguish variant；enough memory to hold the largest variant

##### Rich Data Structure with Enums

```rust
enum Json {
    Null,
    Boolean(bool),
    Number(f64),
    String(String),
    Array(Vec<Json>),
    Object(Box<HashMap<String, Json>>)
}
```

##### Generic Enums

```rust
pub enum Option<T> {
    None, Some(T),
}
pub enum Result<T, E> {
    Ok(T), Err(E),
}
```

- 如果T是ref、Box、其他smart pointer，Rust编译器会消除Option\<T\>表示中的tag（0表示None，非0表示pointer）

##### Enums存在的一个问题

- 判断ET类型变量e是ET中的哪一个variant：pattern matching

### 10 模式匹配

##### Enum

```rust
impl TimeUnit {
    pub fn plural(self) -> &'static str {
        match self {
			TimeUnit::Second => "seconds",
            TimeUnit::Minute => "minutes",
            TimeUnit::Hour => "hours",
    }
}
```

```rust
impl RoughTime {
	pub fn to_english(self) -> String {
        match self {
            RoughTime::InThePast(TimeUnit::Hour, 1) => {},
            RoughTime::InThePast(unit, 1) => {},
            RoughTime::InThePast(unit, count) => {},
        }
    }
}
```

##### literal pattern, variable pattern, wildcard pattern

- literal pattern, variable pattern

```rust
match x {
    0 => {},
    n => pritln!("{}", n),
}
```

- wildcard pattern

```rust
match x {
    0 => {},
    _ => {},
}
```

##### tuple pattern, struct pattern

- tuple pattern

```rust 
match (x.cmp(&0), y.cmp(&0)) {
    (Equal, Equal) => {},
    (_, Equal) => {},
    _ => {},
}
```

- struct pattern

```rust
match s {
    Point { x: 0, y: height } => {},
    Point { x: x, y: y } => {}, //等价于Point { x, y }
}
```

```rust
match s {
    Account { name, language, id: _, status: _, address: _ } => {},
    ...
}
match s {
    Account { name, language, .. } => {}, //..省略符
    ...
}
```

##### array pattern, slice pattern

```rust
match a {
    [_, _, 0] => [0, 0, 0],
    ...
}
```

```rust
match a {
	[] => {},
    [x] => {},
    [x, y] => {},
    [x, .., y] => {},
}
```

##### reference pattern

```rust
match account {
    Account { name, .. } => {
        f(&name);
        g(account); //假设name不是copy type，error
    }
}
match account {
	Account { ref name, ref mut x, .. } => {
        f(name); //以引用方式指向匹配的值
        g(account); //ok
    }
}
```

- & pattern

```rust
match s.center() { //假设返回引用&Pointer
    &Pointer { x, y } => {} //若x, y不是copy type则编译错误，无法从共享引用中move out一个值
}
```

##### Match Guards

```rust
fn f(x: i64) {
    match s {
        None => {},
        Some(x) => {}, //一个全新的变量覆盖x
        Some(other) => {},
    }
}
```

```rust
fn f(x: i64) {
    match s {
        None => {},
        Some(y) if y == x => {},
        Some(y) => {},
    }
}
```

##### Matching Multiple Possibilities

```rust
match c {
    'a'..='z' | 'A'..='Z' => {},
    '0'..='9' => {},
    _ => {},
}
```

##### Bingding with @ Patterns

```rust
match s {
    Shape::Rect(top_left, bottom_right) => {
        paint(&Shape::Rect(top_left, bottom_right))
    }
    _ {}
}
```

```rust
match s {
    rect @ Shape::Rect(..) => {
        paint(&rect)
    }
    _ {}
}
```

##### Pattern Matching 其他可以使用的地方

```rust
let Track { album, title, .. } = song; 

fn dis((x, y): (f64, f64)) {}

for (id, d) in &cache_map {}

let sum = numbers.fold(0, |a, &num| a + num);

if let Some(_) = x {}

while let Err(err) = f() {}
```

##### Binary Tree 示例

```rust
impl<T: Ord> BinaryTree<T> {
    fn add(&mut self, value: T) {
        match *self {
            BinaryTree::Empty => {
                *self = BinaryTree::NonEmpty(Box::new(TreeNode {
                    element: value,
                    left: BinaryTree::Empty,
                    right: BinaryTree::Empty,
                }))
            }
            BinaryTree::NonEmpty(ref mut node) => {
                if value <= node.element {
                    node.left.add(value);
                }
                else {
                    node.right.add(value);
                }
            }
        }
    }
}
```

### 11 Trait and Generic

##### Trait

- 定义示例

```rust
pub trait Write {
    ...
}
```

- 使用示例

```rust
//Trait Object
fn say_hello(out: &mut dyn Write) -> std::io::Result<()> {}

let mut bytes = vec![]; //实现了Write
let mut file = File::create("hello.txt")?; //实现了Write

say_hello(&mut bytes)?;
sya_hello(&mut file)?;
```

```rust
//Trait Bound on type parameters in generic functions
fn min<T: Ord>(value1: T, value2: T) -> T {}
```

##### Trait的使用

- 需要确保trait被引入到当前作用域

  一个类型可能实现多个trait，显式引入所需trait减少名称冲突

  std::prelude已经引入很多traits

- Trait Object

  a ref to a value with a trait type

  vtable、data

```rust
let writer: dy Write = buf; //error
let writer: &mut dyn Write = &mut buf;
```

```rust
//自动转换
say_hello(&mut file)?;
let w: Box<dy Write> = Box::new(file);
```

- Trait Object VS Type Parameter

  Trait Object：Dynamic Dispatch（在运行时刻查找vtable确定调用方法的地址）

  Type Parameter：Static Dispatch（在编译时刻确定调用方法的地址）

- Generic function

```rust
let v1 = (0..1000).collect(); //error
let v2: Vec<i32> = (0..1000).colloct(); //ok
let v3: (0..1000).collect::<Vec<i32>>(); //ok
```

```rust
fn f<T: Debug + Hash + Eq>() {}
fn f<T>() 
	where T: Debug + Hash + Eq 
{}
```

```rust
//Lifetiem parameter需要放在Type parameter之前
fn f<'t, 'c, P>() {}
```












































