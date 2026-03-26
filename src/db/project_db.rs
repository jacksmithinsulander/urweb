//! [`ProjectDb`] enum and [`DatabaseBackend`] trait.
//!
//! **Persy / RocksDB / ndb / TigerBeetle** select **native** C clients (distinct headers,
//! linker flags, and non-relational DDL). Relational SQL IR remains tied to [`ProjectDb::Sql`]
//! flavors until lowering to native KV/ledger operations exists.

use anyhow::Result;

// ---------------------------------------------------------------------------
// SQL dialect (codegen-supported)
// ---------------------------------------------------------------------------

/// Relational SQL backend Ur/Web can emit DDL and C clients for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SqlFlavor {
    Sqlite,
    Mysql,
    Postgresql,
}

impl SqlFlavor {
    pub const fn wire_name(self) -> &'static str {
        match self {
            SqlFlavor::Sqlite => "sqlite",
            SqlFlavor::Mysql => "mysql",
            SqlFlavor::Postgresql => "postgres",
        }
    }
}

// ---------------------------------------------------------------------------
// Full project DB choice
// ---------------------------------------------------------------------------

/// Backend selected for the project (`-dbms` / `.urp` `dbms`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProjectDb {
    Sql(SqlFlavor),
    Persy,
    Rocksdb,
    Ndb,
    Tigerbeetle,
}

/// LangSec / lexer profile (manifest-driven; matches [`ProjectDb`] class).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangsecParseProfile {
    RelationalSql,
    KeyValueStore,
    Ledger,
}

impl Default for ProjectDb {
    /// Legacy `dbms == ""`: Postgres-style DDL and C `libpq` path.
    fn default() -> Self {
        ProjectDb::Sql(SqlFlavor::Postgresql)
    }
}

/// Backends with relational SQL codegen in `cjr_print` / `sql_generate`.
pub const SQL_BACKENDS: &[&str] = &["sqlite", "mysql", "postgres"];

/// Native / non-relational `-dbms` names (KV or ledger clients — not `ProjectDb::Sql`).
pub const NON_SQL_BACKENDS: &[&str] = &["persy", "rocksdb", "ndb", "tigerbeetle"];

/// Reference URLs for the products behind [`NON_SQL_BACKENDS`] (documentation only).
pub const NON_SQL_BACKEND_DOC_MARKERS: &[(&str, &str)] = &[
    ("persy", "persy.rs"),
    ("rocksdb", "github.com/facebook/rocksdb"),
    ("ndb", "9fans.github.io/plan9port/man/man7/ndb.html"),
    ("tigerbeetle", "tigerbeetle.com"),
];

/// Alias; same slice as [`NON_SQL_BACKENDS`].
pub const KV_BACKENDS: &[&str] = NON_SQL_BACKENDS;

/// All accepted `-dbms` spellings (lowercase), for help / errors.
pub const KNOWN_DB_NAMES: &[&str] = &[
    "sqlite",
    "mysql",
    "postgres",
    "persy",
    "rocksdb",
    "ndb",
    "tigerbeetle",
];

impl ProjectDb {
    #[inline]
    pub fn langsec_parse_profile(self) -> LangsecParseProfile {
        match self {
            ProjectDb::Sql(_) => LangsecParseProfile::RelationalSql,
            ProjectDb::Persy | ProjectDb::Rocksdb | ProjectDb::Ndb => {
                LangsecParseProfile::KeyValueStore
            }
            ProjectDb::Tigerbeetle => LangsecParseProfile::Ledger,
        }
    }

    /// When false, [`crate::c_like_representation::sql_generate`] emits a placeholder instead of DDL.
    #[inline]
    pub fn emits_foreign_relational_sql_ddl(self) -> bool {
        matches!(self, ProjectDb::Sql(_))
    }

    pub fn sqlite() -> Self {
        ProjectDb::Sql(SqlFlavor::Sqlite)
    }

    pub fn mysql() -> Self {
        ProjectDb::Sql(SqlFlavor::Mysql)
    }

    pub fn postgres() -> Self {
        ProjectDb::Sql(SqlFlavor::Postgresql)
    }

    /// Native backends that inject [`UrwebNative`](crate::compiler) FFI shims and runtime C ops.
    #[inline]
    pub const fn exposes_urweb_native_surface(self) -> bool {
        matches!(
            self,
            ProjectDb::Persy | ProjectDb::Rocksdb | ProjectDb::Ndb | ProjectDb::Tigerbeetle
        )
    }

    /// Parse a non-empty `-dbms` / `.urp` token (ASCII case-insensitive).
    pub fn parse_user_input(input: &str) -> Result<Self, String> {
        let s = input.trim();
        if s.is_empty() {
            return Err("dbms name must not be empty".into());
        }
        if s.eq_ignore_ascii_case("sqlite") {
            return Ok(ProjectDb::sqlite());
        }
        if s.eq_ignore_ascii_case("mysql") {
            return Ok(ProjectDb::mysql());
        }
        if s.eq_ignore_ascii_case("postgres") {
            return Ok(ProjectDb::postgres());
        }
        if s.eq_ignore_ascii_case("persy") {
            return Ok(ProjectDb::Persy);
        }
        if s.eq_ignore_ascii_case("rocksdb") {
            return Ok(ProjectDb::Rocksdb);
        }
        if s.eq_ignore_ascii_case("ndb") {
            return Ok(ProjectDb::Ndb);
        }
        if s.eq_ignore_ascii_case("tigerbeetle") {
            return Ok(ProjectDb::Tigerbeetle);
        }
        Err(format!(
            "unknown dbms '{input}' (known: {})",
            KNOWN_DB_NAMES.join(", ")
        ))
    }

    /// Wire name for SQL-oriented tooling: `sqlite` / `mysql` / `postgres`, or `None` for native stores.
    pub fn sql_wire_name(&self) -> Option<&'static str> {
        match self {
            ProjectDb::Sql(f) => Some(f.wire_name()),
            ProjectDb::Persy | ProjectDb::Rocksdb | ProjectDb::Ndb | ProjectDb::Tigerbeetle => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

/// Shared behavior for linker flags, SQL codegen gating, and dialect checks.
pub trait DatabaseBackend {
    fn canonical_name(&self) -> &'static str;
    fn require_sql_code_generation(&self) -> Result<()>;
    fn link_library_flag(&self) -> &'static str;

    /// MySQL-specific escaping / mangling.
    fn is_mysql(&self) -> bool;
    fn is_sqlite(&self) -> bool;
    /// Postgres-style DDL (includes legacy `dbms == ""`).
    fn is_postgres_family(&self) -> bool;
}

impl DatabaseBackend for ProjectDb {
    fn canonical_name(&self) -> &'static str {
        match self {
            ProjectDb::Sql(SqlFlavor::Sqlite) => "sqlite",
            ProjectDb::Sql(SqlFlavor::Mysql) => "mysql",
            ProjectDb::Sql(SqlFlavor::Postgresql) => "postgres",
            ProjectDb::Persy => "persy",
            ProjectDb::Rocksdb => "rocksdb",
            ProjectDb::Ndb => "ndb",
            ProjectDb::Tigerbeetle => "tigerbeetle",
        }
    }

    fn require_sql_code_generation(&self) -> Result<()> {
        let _ = self;
        Ok(())
    }

    fn link_library_flag(&self) -> &'static str {
        match self {
            ProjectDb::Sql(SqlFlavor::Sqlite) => "-lsqlite3",
            ProjectDb::Sql(SqlFlavor::Mysql) => "-lmysqlclient",
            ProjectDb::Sql(SqlFlavor::Postgresql) => "-lpq",
            ProjectDb::Persy => "-lurweb_persy",
            ProjectDb::Rocksdb => "-lrocksdb -lstdc++",
            ProjectDb::Ndb => "-lurweb_ndb",
            ProjectDb::Tigerbeetle => "-ltb_client",
        }
    }

    fn is_mysql(&self) -> bool {
        matches!(self, ProjectDb::Sql(SqlFlavor::Mysql))
    }

    fn is_sqlite(&self) -> bool {
        matches!(self, ProjectDb::Sql(SqlFlavor::Sqlite))
    }

    fn is_postgres_family(&self) -> bool {
        matches!(self, ProjectDb::Sql(SqlFlavor::Postgresql))
    }
}

/// Legacy helper: parse CLI / job token to static name (for logging only).
pub fn canonical_dbms(input: &str) -> Result<&'static str, String> {
    Ok(ProjectDb::parse_user_input(input)?.canonical_name())
}
