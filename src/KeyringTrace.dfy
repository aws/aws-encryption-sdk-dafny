include "AwsCrypto.dfy"

module KeyringTraceModule {
  import opened Aws

  datatype KeyringTrace = KeyringTrace(wrapping_key_namespace: string, wrapping_key_name: string, flags: bv32)

  /**
  * Bit flag indicating this wrapping key generated a new data key.
  */
  const AWS_CRYPTOSDK_WRAPPING_KEY_GENERATED_DATA_KEY: bv32 := 1 << 0

  /**
  * Bit flag indicating this wrapping key encrypted a data key.
  */
  const AWS_CRYPTOSDK_WRAPPING_KEY_ENCRYPTED_DATA_KEY: bv32 := 1 << 1

  /**
  * Bit flag indicating this wrapping key decrypted a data key.
  */
  const AWS_CRYPTOSDK_WRAPPING_KEY_DECRYPTED_DATA_KEY: bv32 := 1 << 2

  /**
  * Bit flag indicating this wrapping key signed the encryption context.
  */
  const AWS_CRYPTOSDK_WRAPPING_KEY_SIGNED_ENC_CTX: bv32 := 1 << 3

  /**
  * Bit flag indicating this wrapping key verified signature of encryption context.
  */
  const AWS_CRYPTOSDK_WRAPPING_KEY_VERIFIED_ENC_CTX: bv32 := 1 << 4

  method keyring_trace_add_record(trace: seq<KeyringTrace>, wrapping_key_namespace: string, wrapping_key_name: string, flags: bv32) returns (result: Outcome, trace': seq<KeyringTrace>)
  {
    trace' := trace + [KeyringTrace(wrapping_key_namespace, wrapping_key_name, flags)];
    result := AWS_OP_SUCCESS;
  }

  method keyring_trace_init() returns (result: Outcome, trace': seq<KeyringTrace>) {
    return AWS_OP_SUCCESS, [];
  }

  method keyring_trace_clean_up(trace: seq<KeyringTrace>) {}
  method keyring_trace_clear(trace: seq<KeyringTrace>) {}
}
