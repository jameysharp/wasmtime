use wasmtime::component::ComponentEnum;

#[derive(ComponentEnum)]
enum TestEnum {
    A,
    B,
}

/*
#[derive(ComponentEnum)]
struct NotEnum {
    a: i32,
}
*/

fn main() {}
