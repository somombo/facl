/** The request facts a policy can read. */
export interface Footprint {
  readonly headers: boolean;
  readonly auth: boolean;
  readonly context: boolean;
}

/** Raw facts, in the shape the engine reads. */
export interface Facts {
  method: string;
  /** The percent-encoded path a router dispatches on, without a query. */
  path: string;
  headers?: Record<string, string>;
  auth?: Record<string, unknown> | null;
  context?: Record<string, unknown> | null;
}

export type DenyReason =
  | "no_matching_rule"
  | "no_allow_for_method"
  | "conditions_not_met"
  | "bad_request_path"
  | "internal_error";

export interface Decision {
  allowed: boolean;
  /** Null when allowed. Log it; do not show it to clients. */
  reason: DenyReason | null;
}

/** One problem found in a rules file. Lines and columns are 1-based. */
export interface Diagnostic {
  severity: "error" | "warning";
  message: string;
  line: number;
  col: number;
}

/** The error thrown by `compile` when the rules are rejected. */
export interface CompileError extends Error {
  diagnostics: Diagnostic[];
}

export interface Policy {
  readonly footprint: Footprint;
  /** Decides raw facts. Throws when the facts are unusable. */
  evaluate(facts: Facts): { allowed: boolean; reason: string | null };
}

export interface AuthorizeOptions {
  /** Verifies credentials; returns `{ uid, ... }` or null. Called only if the policy reads `request.auth`. */
  auth?: (request: Request) => unknown | Promise<unknown>;
  /** Application facts, or a function producing them. Used only if the policy reads `context`. */
  context?:
    | Record<string, unknown>
    | ((request: Request) => Record<string, unknown> | Promise<Record<string, unknown>>);
}

/** Compiles a rules file. Throws a `CompileError` when it is rejected. */
export function compile(source: string): Policy;

/** Decides a Fetch `Request`. Never throws; failures deny with `internal_error`. */
export function authorize(
  policy: Policy,
  request: Request,
  options?: AuthorizeOptions,
): Promise<Decision>;
