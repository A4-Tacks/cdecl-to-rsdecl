Convert some C declaration into Rust style declaration

Rust style declaration uses prefix specifiers and full parentheses
to quickly understand deep nested structures

# Not Supported

- Due to the inability to retrieve symbols in the context,
  named parameters for functions are not supported
- It is not recommended to leave spaces before function syntax,
  as ambiguity may lead to strange results

  such as `size_t f(size_t)` -> `f: fn(size_t) -> size_t`,
  but `size_t f (size_t)` -> `size_t: size_t f`,

# Examples

```c
$ cargo run --
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.54s
     Running `target/debug/cdecl-to-rsdecl`
Welcome to cdecl-to-rsdecl, input `exit` to exit
> int *const (*p)[4]
p: *[const*int; 4];
> void (*signal(int, void (*)(int)))(int)
signal: fn(int, *fn(int)) -> *fn(int);
> void (*signal(int, void (*)(int)))(int), f();
signal: fn(int, *fn(int)) -> *fn(int);
f: fn();
> struct foo a, **b, c[3], (*d)()
a: struct foo;
b: **struct foo;
c: [struct foo; 3];
d: *fn() -> struct foo;
```

```c
$ cargo run -- -c
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.21s
     Running `target/debug/cdecl-to-rsdecl -c`
Welcome to cdecl-to-rsdecl, input `exit` to exit
> p: *const*const char
const char *const *p;
> signal: fn(int, *fn(int)) -> *fn(int)
void (*signal(int, void (*)(int)))(int);
```
