use anyval::{Map, Value, array, map};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

fn bench_map_macro(c: &mut Criterion) {
    let mut group = c.benchmark_group("map_macro");
    group.bench_function("empty", |b| b.iter(|| map! {}));
    group.bench_function("single", |b| b.iter(|| map! { "key" => "value" }));
    group.bench_function("multiple", |b| {
        b.iter(|| {
            map! {
                "name" => "Alice",
                "age" => 30,
                "active" => true,
                "score" => 99.5,
            }
        })
    });
    group.finish();
}

fn bench_array_macro(c: &mut Criterion) {
    let mut group = c.benchmark_group("array_macro");
    group.bench_function("empty", |b| b.iter(|| array![]));
    group.bench_function("single", |b| b.iter(|| array![42]));
    group.bench_function("mixed", |b| b.iter(|| array!["hello", 42, true, 3.14]));
    group.finish();
}

fn bench_indexing(c: &mut Criterion) {
    let m = map! {
        "num" => 123,
        "text" => "hello",
        "flag" => true,
    };
    let a = array![1, 2, 3, 4, 5];

    let mut group = c.benchmark_group("indexing");
    group.bench_function("map_get", |b| b.iter(|| m["num"].as_int()));
    group.bench_function("array_get", |b| b.iter(|| a[2].as_int()));
    group.finish();
}

#[cfg(all(feature = "json"))]
fn bench_json(c: &mut Criterion) {
    let m = map! {
        "name" => "Alice",
        "age" => 30,
        "active" => true,
        "scores" => array![10, 20, 30],
    };
    let json_str = m.to_json().unwrap();

    let mut group = c.benchmark_group("json");
    group.bench_function("serialize", |b| b.iter(|| m.to_json()));
    group.bench_function("deserialize", |b| b.iter(|| Map::from_json(&json_str)));
    group.finish();
}

fn bench_map_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("map_creation");
    for size in [1, 10, 100].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let mut m = Map::new();
                for i in 0..size {
                    m.insert(format!("key{}", i), Value::Int(i as i64));
                }
                m
            });
        });
    }
    group.finish();
}

fn bench_web_json_map_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("web_json_map_creation");
    group.bench_function("user_object", |b| {
        b.iter(|| {
            map! {
                "id" => 123,
                "name" => "John Doe",
                "email" => "john@example.com",
                "age" => 30,
                "active" => true,
                "created_at" => "2023-01-01T00:00:00Z",
                "roles" => array!["admin", "user"],
            }
        })
    });
    group.finish();
}

// Register the benchmarks
criterion_group!(
    benches,
    bench_map_macro,
    bench_array_macro,
    bench_indexing,
    bench_json,
    bench_map_creation,
    bench_web_json_map_creation,
);
criterion_main!(benches);
