use std::fs;
use std::path::Path;
use std::process::Command;
use serde_json::Value;

#[test]
fn test_unigram_expectations() {
    // Path to your probs_*.json files
    let probs_dir = Path::new("data/origami/probs_set");

    for entry in fs::read_dir(probs_dir).unwrap() {
        let path = entry.unwrap().path();
        if !path.extension().map(|e| e == "json").unwrap_or(false) {
            continue;
        }

        let file_contents = fs::read_to_string(&path).unwrap();
        let parsed: Value = serde_json::from_str(&file_contents).unwrap();

        let unigrams_path = &path; // pass full path to binary
        let expected = parsed["expected"].as_object().unwrap();

        for (task_name, expected_prog) in expected {
            let output = Command::new("target/release/top_down")
                .arg("data/origami/tasks.json")
                .arg("--domain").arg("list")
                .arg("--model").arg("unigram")
                .arg("--unigrams-path").arg(unigrams_path)
                .arg("--threads").arg("1")
                .arg("--filter").arg(task_name)
                .output()
                .expect("Failed to run top_down");

            assert!(
                output.status.success(),
                "top_down failed on task '{}': {}",
                task_name,
                String::from_utf8_lossy(&output.stderr)
            );

            let stdout = String::from_utf8_lossy(&output.stdout);
            // Find the last solution line for the current task
            let actual = stdout
                .lines()
                .rev()
                .find_map(|line| {
                    if line.contains("Solutions:") && line.contains(task_name) {
                        // Try to extract the program from this line
                        // line.split('@').last()?.trim().strip_prefix('(').map(|s| format!("({}", s))
                        line.split('@').last().map(str::trim)
                    } else {
                        None
                    }
                })
                .expect(&format!("No solution line found for task '{}' in output:\n{}", task_name, stdout));

            let expected_str = expected_prog.as_str().unwrap();
            assert!(
                actual == expected_str,
                "Mismatch for task '{}':\nExpected: {}\nActual:   {}\nFile:     {}",
                task_name,
                expected_str,
                actual,
                path.display()
            );
        }
    }
}
