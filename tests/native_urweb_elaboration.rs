//! Fast checks for compiler-injected `UrwebNative` (`urweb_*`) with boot + native `dbms`.
//! These assert the injected surface is present, opened, and curried with the expected arity.

mod common;

use std::path::PathBuf;
use std::sync::OnceLock;

use ur::compiler;
use ur::elaborated::{Constructor, Signature, SignatureItem};
use ur::error_types::ErrorReporter;
use ur::settings::Settings;
use ur::source::File as SourceFile;

#[derive(Clone, Copy)]
enum NativeBackend {
    Ndb,
    TigerBeetle,
}

impl NativeBackend {
    fn urp_body(self) -> &'static str {
        match self {
            NativeBackend::Ndb => "dbms ndb\ndatabase :memory:\n\nm\n",
            NativeBackend::TigerBeetle => "dbms tigerbeetle\ndatabase 127.0.0.1:3000\n\nm\n",
        }
    }

    fn label(self) -> &'static str {
        match self {
            NativeBackend::Ndb => "ndb",
            NativeBackend::TigerBeetle => "tigerbeetle",
        }
    }
}

static NATIVE_WORKSPACE_ROOT: OnceLock<Option<PathBuf>> = OnceLock::new();
static CACHED_NATIVE_BASIS_SOURCES: OnceLock<Option<SourceFile>> = OnceLock::new();
static CACHED_NDB_BOOT_SNAPSHOT: OnceLock<Result<compiler::BootElaborationSnapshot, String>> =
    OnceLock::new();
static CACHED_TIGERBEETLE_BOOT_SNAPSHOT: OnceLock<
    Result<compiler::BootElaborationSnapshot, String>,
> = OnceLock::new();

fn native_workspace_root() -> Option<&'static PathBuf> {
    NATIVE_WORKSPACE_ROOT
        .get_or_init(|| {
            let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            if root.join("lib/ur/basis.urs").is_file() {
                Some(root)
            } else {
                None
            }
        })
        .as_ref()
}

fn get_cached_native_basis_sources() -> Option<&'static SourceFile> {
    CACHED_NATIVE_BASIS_SOURCES
        .get_or_init(|| {
            let root = native_workspace_root()?;
            let settings = Settings::new();
            let mut errors = ErrorReporter::new_silent();
            compiler::parse_basis_sources(root, &settings, &mut errors)
        })
        .as_ref()
}

fn build_native_boot_snapshot(
    backend: NativeBackend,
) -> Result<compiler::BootElaborationSnapshot, String> {
    let cached_boot = match get_cached_native_basis_sources() {
        Some(cached_boot) => cached_boot,
        None => {
            return Err("native boot root not found (lib/ur/basis.urs missing)".to_string());
        }
    };

    let dir = common::tempdir("native boot snapshot tempdir");
    let root = dir.path();
    let urp_path = root.join("app.urp");
    common::write_file(
        &urp_path,
        backend.urp_body(),
        "write app.urp for native boot snapshot",
    );

    let (job, settings) =
        compiler::resolve_project_job_and_settings(&urp_path).map_err(|error| {
            format!(
                "resolve_project_job_and_settings for {} snapshot: {error}",
                backend.label(),
            )
        })?;

    let mut errors = ErrorReporter::new_silent();
    match compiler::elaborate_boot_snapshot_with_project_prelude(
        cached_boot,
        &job,
        &settings,
        &mut errors,
    ) {
        Some(snapshot) => Ok(snapshot),
        None => Err(format!(
            "elaborate_boot_snapshot_with_project_prelude for {} snapshot: {errors:?}",
            backend.label(),
        )),
    }
}

fn get_cached_native_boot_snapshot(
    backend: NativeBackend,
) -> Result<&'static compiler::BootElaborationSnapshot, String> {
    if native_workspace_root().is_none() {
        return Err("native boot root not found (lib/ur/basis.urs missing)".to_string());
    }

    let cache = match backend {
        NativeBackend::Ndb => &CACHED_NDB_BOOT_SNAPSHOT,
        NativeBackend::TigerBeetle => &CACHED_TIGERBEETLE_BOOT_SNAPSHOT,
    };
    match cache.get_or_init(|| build_native_boot_snapshot(backend)) {
        Ok(snapshot) => Ok(snapshot),
        Err(error) => Err(error.clone()),
    }
}

fn urweb_native_value_arity(
    snapshot: &compiler::BootElaborationSnapshot,
    value_name: &str,
) -> Result<usize, String> {
    let Some((_structure_id, signature)) = snapshot.environment.lookup_str("UrwebNative") else {
        return Err("UrwebNative structure is missing from the elaborated environment".to_string());
    };

    let Signature::Const(signature_items) = &signature.node else {
        return Err("UrwebNative signature is not a constant signature".to_string());
    };

    let value_type =
        match signature_items
            .iter()
            .find_map(|signature_item| match &signature_item.node {
                SignatureItem::Val(name, _id, value_type) if name == value_name => Some(value_type),
                _ => None,
            }) {
            Some(value_type) => value_type,
            None => {
                return Err(format!(
                    "UrwebNative signature does not expose `{value_name}`",
                ));
            }
        };

    let mut arity = 0;
    let mut current_type = value_type;
    while let Constructor::TFun(_argument_type, result_type) = &current_type.node {
        arity += 1;
        current_type = result_type;
    }
    Ok(arity)
}

fn boot_snapshot_opens_urweb_native(snapshot: &compiler::BootElaborationSnapshot) -> bool {
    snapshot.seed_steps.iter().any(|step| match step {
        ur::elaborated::elaborate::BootSeedStep::Open { path, .. } => {
            path.len() == 1 && path[0] == "UrwebNative"
        }
        _ => false,
    })
}

#[test]
fn native_ndb_urweb_put_get_elaborates_under_boot() {
    let snapshot = match get_cached_native_boot_snapshot(NativeBackend::Ndb) {
        Ok(snapshot) => snapshot,
        Err(error) if error.contains("lib/ur/basis.urs missing") => return,
        Err(error) => panic!("load native NDB boot snapshot: {error}"),
    };

    match (
        boot_snapshot_opens_urweb_native(snapshot),
        urweb_native_value_arity(snapshot, "urweb_put"),
        urweb_native_value_arity(snapshot, "urweb_get"),
    ) {
        (true, Ok(2), Ok(1)) => {}
        (false, _, _) => panic!("native NDB boot snapshot must open UrwebNative"),
        (_, Err(error), _) => panic!("native NDB `urweb_put` surface missing: {error}"),
        (_, _, Err(error)) => panic!("native NDB `urweb_get` surface missing: {error}"),
        (_, Ok(put_arity), Ok(get_arity)) => panic!(
            "native NDB surface has wrong arity: urweb_put={put_arity}, urweb_get={get_arity}",
        ),
    }
}

#[test]
fn native_ndb_urweb_put_partial_application_elaborates_under_boot() {
    let snapshot = match get_cached_native_boot_snapshot(NativeBackend::Ndb) {
        Ok(snapshot) => snapshot,
        Err(error) if error.contains("lib/ur/basis.urs missing") => return,
        Err(error) => panic!("load native NDB boot snapshot: {error}"),
    };

    match urweb_native_value_arity(snapshot, "urweb_put") {
        Ok(2) => {}
        Ok(arity) => panic!("native NDB `urweb_put` must stay curried with arity 2, got {arity}"),
        Err(error) => panic!("native NDB `urweb_put` arity lookup failed: {error}"),
    }
}

#[test]
fn native_tigerbeetle_urweb_tb_transfer_elaborates_under_boot() {
    let snapshot = match get_cached_native_boot_snapshot(NativeBackend::TigerBeetle) {
        Ok(snapshot) => snapshot,
        Err(error) if error.contains("lib/ur/basis.urs missing") => return,
        Err(error) => panic!("load native TigerBeetle boot snapshot: {error}"),
    };

    match (
        boot_snapshot_opens_urweb_native(snapshot),
        urweb_native_value_arity(snapshot, "urweb_tb_transfer"),
    ) {
        (true, Ok(4)) => {}
        (false, _) => panic!("native TigerBeetle boot snapshot must open UrwebNative"),
        (_, Err(error)) => {
            panic!("native TigerBeetle `urweb_tb_transfer` surface missing: {error}",)
        }
        (_, Ok(arity)) => panic!(
            "native TigerBeetle `urweb_tb_transfer` must stay curried with arity 4, got {arity}",
        ),
    }
}

#[test]
fn native_tigerbeetle_urweb_tb_transfer_curried_elaborates_under_boot() {
    let snapshot = match get_cached_native_boot_snapshot(NativeBackend::TigerBeetle) {
        Ok(snapshot) => snapshot,
        Err(error) if error.contains("lib/ur/basis.urs missing") => return,
        Err(error) => panic!("load native TigerBeetle boot snapshot: {error}"),
    };

    match urweb_native_value_arity(snapshot, "urweb_tb_transfer") {
        Ok(4) => {}
        Ok(arity) => {
            panic!("native TigerBeetle `urweb_tb_transfer` must stay curried with arity 4, got {arity}")
        }
        Err(error) => panic!("native TigerBeetle `urweb_tb_transfer` arity lookup failed: {error}"),
    }
}
