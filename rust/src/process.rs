use anyhow::{Context, Result};
use serde::Serialize;
use std::{
    fs::File,
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};

#[derive(Debug, Clone, Serialize)]
pub struct Output {
    pub exit_code: Option<i32>,
    pub timed_out: bool,
    pub stdout: String,
    pub stderr: String,
    pub elapsed_ms: u128,
}

pub fn run(command: &mut Command, seconds: u64) -> Result<Output> {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    let stdout = tempfile::tempfile()?;
    let stderr = tempfile::tempfile()?;
    let mut out_read = stdout.try_clone()?;
    let mut err_read = stderr.try_clone()?;
    command
        .stdin(Stdio::null())
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr));
    let start = Instant::now();
    let mut child = command.spawn().context("could not start subprocess")?;
    let (status, timed_out) = loop {
        if let Some(status) = child.try_wait()? {
            break (status, false);
        }
        if start.elapsed() >= Duration::from_secs(seconds) {
            #[cfg(unix)]
            {
                // The unreaped child's PID is reserved, and process_group(0)
                // made it the leader of a new group before exec.
                let killed = unsafe { libc::kill(-(child.id() as i32), libc::SIGKILL) };
                if killed != 0 {
                    child
                        .kill()
                        .context("could not kill timed-out subprocess group")?;
                }
            }
            #[cfg(not(unix))]
            child
                .kill()
                .context("could not kill timed-out subprocess")?;
            break (child.wait()?, true);
        }
        thread::sleep(Duration::from_millis(20));
    };
    fn read(file: &mut File) -> Result<String> {
        use std::io::{Read, Seek, SeekFrom};
        file.seek(SeekFrom::Start(0))?;
        let mut bytes = Vec::new();
        file.take(4 * 1024 * 1024).read_to_end(&mut bytes)?;
        Ok(String::from_utf8_lossy(&bytes).into_owned())
    }
    Ok(Output {
        exit_code: status.code(),
        timed_out,
        stdout: read(&mut out_read)?,
        stderr: read(&mut err_read)?,
        elapsed_ms: start.elapsed().as_millis(),
    })
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    #[test]
    fn times_out_a_process_tree() {
        let output = run(Command::new("sh").args(["-c", "sleep 30 & wait"]), 1).unwrap();
        assert!(output.timed_out);
        assert_ne!(output.exit_code, Some(0));
        assert!(output.elapsed_ms < 3000);
    }
}
