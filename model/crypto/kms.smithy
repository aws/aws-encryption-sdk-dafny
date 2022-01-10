namespace aws.crypto

use aws.polymorph#reference
use aws.polymorph#positional

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
    client: KmsClientReference,
}
