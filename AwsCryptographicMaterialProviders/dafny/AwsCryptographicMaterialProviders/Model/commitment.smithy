namespace aws.cryptography.materialProviders

@readonly
operation ValidateCommitmentPolicyOnEncrypt {
  input: ValidateCommitmentPolicyOnEncryptInput,
  errors: [InvalidAlgorithmSuiteInfoOnEncrypt],
}

@readonly
operation ValidateCommitmentPolicyOnDecrypt {
  input: ValidateCommitmentPolicyOnDecryptInput,
  errors: [InvalidAlgorithmSuiteInfoOnDecrypt],
}

structure ValidateCommitmentPolicyOnEncryptInput {
  @required
  algorithm: AlgorithmSuiteId,
  @required
  commitmentPolicy: CommitmentPolicy,
}

structure ValidateCommitmentPolicyOnDecryptInput {
  @required
  algorithm: AlgorithmSuiteId,
  @required
  commitmentPolicy: CommitmentPolicy,
}

@error("client")
structure InvalidAlgorithmSuiteInfoOnEncrypt {
  @required
  message: String,
}
@error("client")
structure InvalidAlgorithmSuiteInfoOnDecrypt {
  @required
  message: String,
}
