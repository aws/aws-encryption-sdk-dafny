namespace aws.cryptography.materialProviders

use aws.polymorph#reference
use aws.polymorph#positional
use aws.polymorph#extendable

use com.amazonaws.kms#KeyManagementService

///////////////////
// Basic structures

string KmsKeyId

list KmsKeyIdList {
  member: KmsKeyId
}

string Region

list RegionList {
  member: Region
}

string AccountId

list AccountIdList {
  member: AccountId
}

//////////
// Clients

@reference(service: KeyManagementService)
structure KmsClientReference {}

///////////////////
// Client Suppliers

@extendable
resource ClientSupplier {
  operations: [GetClient],
}

@reference(resource: ClientSupplier)
structure ClientSupplierReference {}

operation GetClient {
  input: GetClientInput,
  output: GetClientOutput,
}

structure GetClientInput {
  @required
  region: Region,
}

@positional
structure GetClientOutput {
  @required
  client: KmsClientReference,
}

operation CreateDefaultClientSupplier {
  input: CreateDefaultClientSupplierInput,
  output: CreateDefaultClientSupplierOutput
}

structure CreateDefaultClientSupplierInput {
}

@positional
structure CreateDefaultClientSupplierOutput {
  @required
  client: ClientSupplierReference
}
