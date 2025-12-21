use vstd::prelude::*;
use vstd::multiset::Multiset;
use vstd::assert_seqs_equal;
use deps_hack::{VReplicaSetSpec as OtherVReplicaSetSpec, k8s_openapi};

fn main() {}

verus!{

pub type VReplicaSetStatusView = EmptyStatusView;
pub type ResourceVersion = int;
pub type Value = StringView;
pub type UnmarshalError = ();
pub type StringView = Seq<char>;
pub type PodStatusView = EmptyStatusView;
pub type Uid = int;
pub type RPCId = nat;
pub type EmptyStatusView = ();
pub type StoredState = Map<ObjectRef, DynamicObjectView>;
pub type StatePred<T> = spec_fn(T) -> bool;
pub type InstalledTypes = Map<StringView, InstalledType>;
pub type ExternalLocalState = Value;
pub type ExternalResponse = Value;
pub type ExternalRequest = Value;
pub type ReconcileLocalState = Value;
pub type ReconcileId = nat;

    // File:: ../vstd_ext/seq_lib.rs
#[verifier::external_body]
pub proof fn seq_filter_preserves_no_duplicates<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires s.no_duplicates(),
    ensures s.filter(pred).no_duplicates()
{unimplemented!()}

#[verifier::external_body]
pub proof fn seq_filter_contains_implies_seq_contains<A>(s: Seq<A>, pred: spec_fn(A) -> bool, elt: A)
    requires s.filter(pred).contains(elt),
    ensures s.contains(elt)
{unimplemented!()}

#[verifier::external_body]
pub proof fn true_pred_on_seq_implies_true_pred_on_filtered_seq<A>(s: Seq<A>, pred: spec_fn(A) -> bool, filter_pred: spec_fn(A) -> bool)
    requires forall |e: A| s.contains(e) ==> pred(e),
    ensures forall |e: A| s.filter(filter_pred).contains(e) ==> pred(e)
{unimplemented!()}

#[verifier::external_body]
pub proof fn commutativity_of_seq_map_and_filter<A, B>(s: Seq<A>, pred: spec_fn(A) -> bool, pred_on_mapped: spec_fn(B) -> bool, map: spec_fn(A) -> B)
    // ensure filter on original sequence is identical to filter on mapped sequence
    requires forall |i: int| 0 <= i < s.len() ==> #[trigger] pred(s[i]) == #[trigger] pred_on_mapped(map(s[i])),
    ensures s.map_values(map).filter(pred_on_mapped) == s.filter(pred).map_values(map),
{unimplemented!()}

#[verifier::external_body]
pub proof fn true_pred_on_all_element_equal_to_pred_on_all_index<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        (forall |obj: A| #[trigger] s.contains(obj) ==> pred(obj)) <==> (forall |i: int| 0 <= i < s.len() ==> pred(s[i]))
{unimplemented!()}

#[verifier::external_body]
pub proof fn seq_pred_false_on_all_elements_is_equivalent_to_empty_filter<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures (forall |e: A| #[trigger] s.contains(e) ==> !pred(e)) <==> s.filter(pred).len() == 0,
{unimplemented!()}

#[verifier::external_body]
pub proof fn map_values_to_set_eq_to_set_mk_map_values<A, B>(s: Seq<A>, map: spec_fn(A) -> B)
    ensures s.map_values(map).to_set() == s.to_set().mk_map(map).values(),
{unimplemented!()}

// File: kubernetes_cluster/spec/api_server/types.rs
pub struct APIServerState {
    pub resources: StoredState,
    pub uid_counter: Uid,
    pub resource_version_counter: ResourceVersion,
}

pub struct InstalledType {
    pub unmarshallable_spec: spec_fn(Value) -> bool,
    pub unmarshallable_status: spec_fn(Value) -> bool,
    pub valid_object: spec_fn(DynamicObjectView) -> bool,
    pub valid_transition: spec_fn(DynamicObjectView, DynamicObjectView) -> bool,
    pub marshalled_default_status: spec_fn() -> Value,
}


// File: kubernetes_cluster/spec/controller/types.rs
pub struct ControllerState {
    pub ongoing_reconciles: Map<ObjectRef, OngoingReconcile>,
    pub scheduled_reconciles: Map<ObjectRef, DynamicObjectView>,
    pub reconcile_id_allocator: ReconcileIdAllocator,
}

pub enum RequestContent {
    KubernetesRequest(APIRequest),
    ExternalRequest(ExternalRequest),
}

pub enum ResponseContent {
    KubernetesResponse(APIResponse),
    ExternalResponse(ExternalResponse),
}

pub struct ReconcileIdAllocator {
    pub reconcile_id_counter: ReconcileId,
}

pub struct ReconcileModel {
    pub kind: Kind,
    pub init: spec_fn() -> ReconcileLocalState,
    pub transition: spec_fn(DynamicObjectView, Option<ResponseContent>, ReconcileLocalState) -> (ReconcileLocalState, Option<RequestContent>),
    pub done: spec_fn(ReconcileLocalState) -> bool,
    pub error: spec_fn(ReconcileLocalState) -> bool,
}

pub struct OngoingReconcile {
    pub triggering_cr: DynamicObjectView,
    pub pending_req_msg: Option<Message>,
    pub local_state: ReconcileLocalState,
    pub reconcile_id: ReconcileId,
}

// File: kubernetes_api_objects/exec/api_resource.rs
#[verifier(external_body)]
pub struct ApiResource {
    inner: deps_hack::kube::api::ApiResource,
}
// File: kubernetes_api_objects/spec/api_resource.rs
pub struct ApiResourceView {
    pub kind: Kind,
}



// File: kubernetes_api_objects/exec/resource.rs

macro_rules! implement_field_wrapper_type {
    ($t:ident, $it:ty, $vt:ty) => {
        verus! {

        #[verifier(external_body)]
        pub struct $t {
            inner: $it,
        }

        }

        implement_view_trait!($t, $vt);
        implement_deep_view_trait!($t, $vt);
    };
}


macro_rules! implement_object_wrapper_type {
    ($t:ident, $it:ty, $vt:ty) => {
        implement_field_wrapper_type!($t, $it, $vt);

        verus! {

        impl $t {

            #[verifier(external_body)]
            pub fn metadata(&self) -> (metadata: ObjectMeta)
                ensures metadata@ == self@.metadata,
	{
		unimplemented!()
	}

            #[verifier(external_body)]
            pub fn api_resource() -> (res: ApiResource)
                ensures res@.kind == $vt::kind(),
	{
		unimplemented!()
	}

            #[verifier(external_body)]
            pub fn marshal(self) -> (obj: DynamicObject)
                ensures obj@ == self@.marshal(),
	{
		unimplemented!()
	}

            #[verifier(external_body)]
            pub fn unmarshal(obj: DynamicObject) -> (res: Result<$t, UnmarshalError>)
                ensures
                    res is Ok == $vt::unmarshal(obj@) is Ok,
                    res is Ok ==> res->Ok_0@ == $vt::unmarshal(obj@)->Ok_0,
	{
		unimplemented!()
	}


}}}}

macro_rules! implement_view_trait {
    ($t:ty, $vt:ty) => {
        verus! {

        impl View for $t {
            type V = $vt;

            uninterp spec fn view(&self) -> $vt;
        }

        }
    };
}

macro_rules! implement_deep_view_trait {
    ($t:ty, $vt:ty) => {
        verus! {

        impl DeepView for $t {
            type V = $vt;

            open spec fn deep_view(&self) -> $vt {
                self@
            }
        }

        }
    };
}


implement_view_trait!(ApiResource, ApiResourceView);
implement_deep_view_trait!(ApiResource, ApiResourceView);


// File: kubernetes_api_objects/spec/resource.rs
pub trait Marshallable: Sized {

    spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

}


pub trait ResourceView: Sized {
    type Spec;

    type Status;

    spec fn default() -> Self;

    spec fn metadata(self) -> ObjectMetaView;

    spec fn kind() -> Kind;

    spec fn object_ref(self) -> ObjectRef;

    spec fn spec(self) -> Self::Spec;

    spec fn status(self) -> Self::Status;

    spec fn marshal(self) -> DynamicObjectView;

    spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError>;

    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0;

    proof fn marshal_preserves_metadata()
        ensures forall |d: DynamicObjectView| #[trigger] Self::unmarshal(d) is Ok ==> d.metadata == Self::unmarshal(d)->Ok_0.metadata();

    spec fn marshal_spec(s: Self::Spec) -> Value;

    spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

    spec fn marshal_status(s: Self::Status) -> Value;

    spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

    proof fn marshal_spec_preserves_integrity()
        ensures forall |s: Self::Spec| Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)) is Ok && s == Self::unmarshal_spec(Self::marshal_spec(s))->Ok_0;

    proof fn marshal_status_preserves_integrity()
        ensures forall |s: Self::Status| Self::unmarshal_status(#[trigger] Self::marshal_status(s)) is Ok && s == Self::unmarshal_status(Self::marshal_status(s))->Ok_0;

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status()
        ensures
            // unmarshal is OK iff unmarshal_spec and unmarshaml_status are OK
            forall |obj: DynamicObjectView| obj.kind == Self::kind()
                ==> #[trigger] Self::unmarshal(obj) is Ok == (Self::unmarshal_spec(obj.spec) is Ok && Self::unmarshal_status(obj.status) is Ok),
            // if unmarshal is OK then unmarshalling the spec (status) gives you the spec (status) of the unmarshalled object
            forall |obj: DynamicObjectView| #[trigger] Self::unmarshal(obj) is Ok
                ==> Self::unmarshal_spec(obj.spec)->Ok_0 == Self::unmarshal(obj)->Ok_0.spec()
                    && Self::unmarshal_status(obj.status)->Ok_0 == Self::unmarshal(obj)->Ok_0.status();

    spec fn state_validation(self) -> bool;

}

macro_rules! implement_resource_view_trait {
    ($t:ty, $spec_t:ty, $spec_default:expr, $status_t:ty, $status_default:expr, $kind:expr, $state_validation:ident, $transition_validation:ident) => {
        verus! {

        impl ResourceView for $t {

            type Spec = $spec_t;
            type Status = $status_t;

            open spec fn default() -> Self {
                Self {
                    metadata: ObjectMetaView::default(),
                    spec: $spec_default,
                    status: $status_default,
                }
            }

            open spec fn metadata(self) -> ObjectMetaView {
                self.metadata
            }

            open spec fn kind() -> Kind {
                $kind
            }

            open spec fn object_ref(self) -> ObjectRef {
                ObjectRef {
                    kind: Self::kind(),
                    name: self.metadata().name->0,
                    namespace: self.metadata().namespace->0,
                }
            }

            open spec fn spec(self) -> Self::Spec {
                self.spec
            }

            open spec fn status(self) -> Self::Status {
                self.status
            }

            open spec fn marshal(self) -> DynamicObjectView {
                DynamicObjectView {
                    kind: Self::kind(),
                    metadata: self.metadata(),
                    spec: Self::marshal_spec(self.spec()),
                    status: Self::marshal_status(self.status()),
                }
            }

            open spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError> {
                if obj.kind != Self::kind() {
                    Err(())
                } else if !(Self::unmarshal_spec(obj.spec) is Ok) {
                    Err(())
                } else if !(Self::unmarshal_status(obj.status) is Ok) {
                    Err(())
                } else {
                    Ok(Self {
                        metadata: obj.metadata,
                        spec: Self::unmarshal_spec(obj.spec)->Ok_0,
                        status: Self::unmarshal_status(obj.status)->Ok_0,
                    })
                }
            }

            proof fn marshal_preserves_integrity() {
                Self::marshal_spec_preserves_integrity();
                Self::marshal_status_preserves_integrity();
            }

            proof fn marshal_preserves_metadata() {}


            uninterp spec fn marshal_spec(s: Self::Spec) -> Value;

            uninterp spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

            uninterp spec fn marshal_status(s: Self::Status) -> Value;

            #[verifier(external_body)]
            proof fn marshal_spec_preserves_integrity() {}

            #[verifier(external_body)]
            proof fn marshal_status_preserves_integrity() {}

            uninterp spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

            proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

            open spec fn state_validation(self) -> bool {
                self.$state_validation()
            }

}}}}

// File: kubernetes_cluster/spec/external/types.rs
pub struct ExternalState {
    pub state: ExternalLocalState,
}

pub struct ExternalModel {
    pub init: spec_fn() -> ExternalLocalState,
    pub transition: spec_fn(ExternalRequest, ExternalLocalState, StoredState) -> (ExternalLocalState, ExternalResponse),
}


// File: kubernetes_cluster/spec/network/types.rs
pub struct NetworkState {
    pub in_flight: Multiset<Message>,
}


// File: kubernetes_api_objects/spec/affinity.rs
pub struct AffinityView {}


// File: kubernetes_api_objects/spec/api_method.rs
pub enum APIRequest {
    GetRequest(GetRequest),
    ListRequest(ListRequest),
    CreateRequest(CreateRequest),
    DeleteRequest(DeleteRequest),
    UpdateRequest(UpdateRequest),
    UpdateStatusRequest(UpdateStatusRequest),
    GetThenDeleteRequest(GetThenDeleteRequest),
    GetThenUpdateRequest(GetThenUpdateRequest),
}

pub struct GetRequest {
    pub key: ObjectRef,
}

pub struct ListRequest {
    pub kind: Kind,
    pub namespace: StringView,
}

pub struct CreateRequest {
    pub namespace: StringView,
    pub obj: DynamicObjectView,
}

pub struct DeleteRequest {
    pub key: ObjectRef,
    pub preconditions: Option<PreconditionsView>,
}

pub struct UpdateRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub obj: DynamicObjectView,
}

pub struct UpdateStatusRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub obj: DynamicObjectView,
}

pub struct GetThenDeleteRequest {
    pub key: ObjectRef,
    pub owner_ref: OwnerReferenceView,
}

pub struct GetThenUpdateRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub owner_ref: OwnerReferenceView,
    pub obj: DynamicObjectView,
}

pub enum APIResponse {
    GetResponse(GetResponse),
    ListResponse(ListResponse),
    CreateResponse(CreateResponse),
    DeleteResponse(DeleteResponse),
    UpdateResponse(UpdateResponse),
    UpdateStatusResponse(UpdateStatusResponse),
    GetThenDeleteResponse(GetThenDeleteResponse),
    GetThenUpdateResponse(GetThenUpdateResponse),
}

pub struct GetResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

pub struct ListResponse {
    pub res: Result<Seq<DynamicObjectView>, APIError>,
}

pub struct CreateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

pub struct DeleteResponse {
    pub res: Result<(), APIError>,
}

pub struct UpdateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

pub struct UpdateStatusResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

pub struct GetThenUpdateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

pub struct GetThenDeleteResponse {
    pub res: Result<(), APIError>,
}


// File: kubernetes_api_objects/spec/common.rs
pub enum Kind {
    ConfigMapKind,
    CustomResourceKind(StringView),
    DaemonSetKind,
    PersistentVolumeClaimKind,
    PodKind,
    RoleKind,
    RoleBindingKind,
    StatefulSetKind,
    ServiceKind,
    ServiceAccountKind,
    SecretKind,
}

pub struct ObjectRef {
    pub kind: Kind,
    pub name: StringView,
    pub namespace: StringView,
}


// File: kubernetes_api_objects/spec/container.rs
pub struct ContainerView {
    pub env: Option<Seq<EnvVarView>>,
    pub image: Option<StringView>,
    pub name: StringView,
    pub ports: Option<Seq<ContainerPortView>>,
    pub volume_mounts: Option<Seq<VolumeMountView>>,
    pub lifecycle: Option<LifecycleView>,
    pub resources: Option<ResourceRequirementsView>,
    pub readiness_probe: Option<ProbeView>,
    pub liveness_probe: Option<ProbeView>,
    pub command: Option<Seq<StringView>>,
    pub image_pull_policy: Option<StringView>,
    pub args: Option<Seq<StringView>>,
    pub security_context: Option<SecurityContextView>,
}

pub struct LifecycleView {
    pub pre_stop: Option<LifecycleHandlerView>,
}

pub struct LifecycleHandlerView {
    pub exec_: Option<ExecActionView>,
}

pub struct ContainerPortView {
    pub container_port: int,
    pub name: Option<StringView>,
    pub protocol: Option<StringView>,
}

pub struct VolumeMountView {
    pub mount_path: StringView,
    pub name: StringView,
    pub read_only: Option<bool>,
    pub sub_path: Option<StringView>,
    pub mount_propagation: Option<StringView>,
}

pub struct ProbeView {
    pub exec_: Option<ExecActionView>,
    pub failure_threshold: Option<int>,
    pub initial_delay_seconds: Option<int>,
    pub period_seconds: Option<int>,
    pub success_threshold: Option<int>,
    pub tcp_socket: Option<TCPSocketActionView>,
    pub timeout_seconds: Option<int>,
}

pub struct ExecActionView {
    pub command: Option<Seq<StringView>>,
}

pub struct TCPSocketActionView {
    pub host: Option<StringView>,
    pub port: int,
}

pub struct EnvVarView {
    pub name: StringView,
    pub value: Option<StringView>,
    pub value_from: Option<EnvVarSourceView>,
}

pub struct EnvVarSourceView {
    pub field_ref: Option<ObjectFieldSelectorView>,
}

pub struct SecurityContextView {}

// File: kubernetes_api_objects/exec/dynamic.rs

#[verifier::external_body]
pub struct DynamicObject {
    inner: deps_hack::kube::api::DynamicObject,
}

implement_view_trait!(DynamicObject, DynamicObjectView);
implement_deep_view_trait!(DynamicObject, DynamicObjectView);

// File: kubernetes_api_objects/spec/dynamic.rs
pub struct DynamicObjectView {
    pub kind: Kind,
    pub metadata: ObjectMetaView,
    pub spec: Value,
    pub status: Value,
}

impl DynamicObjectView {

    pub open spec fn object_ref(self) -> ObjectRef
        recommends
            self.metadata.name is Some,
            self.metadata.namespace is Some,
    {
        ObjectRef {
            kind: self.kind,
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

}



// File: kubernetes_api_objects/spec/label_selector.rs
pub struct LabelSelectorView {
    pub match_labels: Option<Map<StringView, StringView>>,
}

impl LabelSelectorView {
    pub open spec fn default() -> LabelSelectorView {
        LabelSelectorView {
            match_labels: None,
        }
    }


    pub open spec fn matches(self, labels: Map<StringView, StringView>) -> bool {
        if self.match_labels is None {
            true
        } else {
            let match_labels = self.match_labels->0;
            forall |k, v| match_labels.contains_pair(k, v) ==> labels.contains_pair(k, v)
        }
    }

}

// File: kubernetes_api_objects/exec/object_meta.rs
implement_field_wrapper_type!(
    ObjectMeta,
    deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta,
    ObjectMetaView
);

// File: kubernetes_api_objects/spec/object_meta.rs
pub struct ObjectMetaView {
    pub name: Option<StringView>,
    pub generate_name: Option<StringView>,
    pub namespace: Option<StringView>,
    pub resource_version: Option<ResourceVersion>,
    pub uid: Option<Uid>,
    pub labels: Option<Map<StringView, StringView>>,
    pub annotations: Option<Map<StringView, StringView>>,
    pub owner_references: Option<Seq<OwnerReferenceView>>,
    pub finalizers: Option<Seq<StringView>>,
    pub deletion_timestamp: Option<StringView>,
}

impl ObjectMetaView {

    pub open spec fn default() -> ObjectMetaView {
        ObjectMetaView {
            name: None,
            generate_name: None,
            namespace: None,
            resource_version: None,
            uid: None,
            labels: None,
            annotations: None,
            owner_references: None,
            finalizers: None,
            deletion_timestamp: None,
        }
    }


    pub open spec fn owner_references_contains(self, owner_ref: OwnerReferenceView) -> bool {
        match self.owner_references {
            Some(owner_refs) => owner_refs.contains(owner_ref),
            None => false,
        }
    }

    pub open spec fn well_formed_for_namespaced(self) -> bool {
        &&& self.name is Some
        &&& self.namespace is Some
        &&& self.resource_version is Some
        &&& self.uid is Some
    }

}



// File: kubernetes_api_objects/spec/owner_reference.rs
pub struct OwnerReferenceView {
    pub block_owner_deletion: Option<bool>,
    pub controller: Option<bool>,
    pub kind: Kind,
    pub name: StringView,
    pub uid: Uid,
}

// File: kubernetes_api_objects/exec/pod.rs
implement_object_wrapper_type!(Pod, k8s_openapi::api::core::v1::Pod, PodView);
implement_field_wrapper_type!(
    PodSpec,
    k8s_openapi::api::core::v1::PodSpec,
    PodSpecView
);


// File: kubernetes_api_objects/spec/pod.rs
pub struct PodView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PodSpecView>,
    pub status: Option<PodStatusView>,
}

implement_resource_view_trait!(PodView, Option<PodSpecView>, None, Option<PodStatusView>, None,
    Kind::PodKind, _state_validation, _transition_validation);

impl PodView {

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

}


pub struct PodSpecView {
    pub affinity: Option<AffinityView>,
    pub containers: Seq<ContainerView>,
    pub volumes: Option<Seq<VolumeView>>,
    pub init_containers: Option<Seq<ContainerView>>,
    pub service_account_name: Option<StringView>,
    pub tolerations: Option<Seq<TolerationView>>,
    pub node_selector: Option<Map<StringView, StringView>>,
    pub runtime_class_name: Option<StringView>,
    pub dns_policy: Option<StringView>,
    pub priority_class_name: Option<StringView>,
    pub scheduler_name: Option<StringView>,
    pub security_context: Option<PodSecurityContextView>,
    pub host_network: Option<bool>,
    pub termination_grace_period_seconds: Option<int>,
    pub image_pull_secrets: Option<Seq<LocalObjectReferenceView>>,
    pub hostname: Option<StringView>,
    pub subdomain: Option<StringView>,
}

pub struct PodSecurityContextView {}

pub struct LocalObjectReferenceView {}


// File: kubernetes_api_objects/spec/pod_template_spec.rs
pub struct PodTemplateSpecView {
    pub metadata: Option<ObjectMetaView>,
    pub spec: Option<PodSpecView>,
}


// File: kubernetes_api_objects/spec/preconditions.rs
pub struct PreconditionsView {
    pub uid: Option<Uid>,
    pub resource_version: Option<ResourceVersion>,
}


// File: kubernetes_api_objects/spec/resource_requirements.rs
pub struct ResourceRequirementsView {
    pub limits: Option<Map<StringView, StringView>>,
    pub requests: Option<Map<StringView, StringView>>,
}


// File: kubernetes_api_objects/spec/toleration.rs
pub struct TolerationView {}


// File: kubernetes_api_objects/spec/volume.rs
pub struct VolumeView {
    pub host_path: Option<HostPathVolumeSourceView>,
    pub config_map: Option<ConfigMapVolumeSourceView>,
    pub name: StringView,
    pub projected: Option<ProjectedVolumeSourceView>,
    pub secret: Option<SecretVolumeSourceView>,
    pub downward_api: Option<DownwardAPIVolumeSourceView>,
    pub empty_dir: Option<EmptyDirVolumeSourceView>,
    pub persistent_volume_claim: Option<PersistentVolumeClaimVolumeSourceView>,
}

pub struct EmptyDirVolumeSourceView {
    pub medium: Option<StringView>,
    pub size_limit: Option<StringView>,
}

pub struct HostPathVolumeSourceView {
    pub path: StringView,
}

pub struct ConfigMapVolumeSourceView {
    pub name: Option<StringView>,
}

pub struct SecretVolumeSourceView {
    pub secret_name: Option<StringView>,
}

pub struct ProjectedVolumeSourceView {
    pub sources: Option<Seq<VolumeProjectionView>>,
}

pub struct VolumeProjectionView {
    pub config_map: Option<ConfigMapProjectionView>,
    pub secret: Option<SecretProjectionView>,
}

pub struct ConfigMapProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

pub struct SecretProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

pub struct KeyToPathView {
    pub key: StringView,
    pub path: StringView,
}

pub struct DownwardAPIVolumeSourceView {
    pub items: Option<Seq<DownwardAPIVolumeFileView>>,
}

pub struct DownwardAPIVolumeFileView {
    pub field_ref: Option<ObjectFieldSelectorView>,
    pub path: StringView,
}

pub struct ObjectFieldSelectorView {
    pub field_path: StringView,
    pub api_version: Option<StringView>,
}

pub struct PersistentVolumeClaimVolumeSourceView {
    pub claim_name: StringView,
    pub read_only: Option<bool>,
}


// File: kubernetes_cluster/spec/cluster.rs
pub struct ClusterState {
    pub api_server: APIServerState,
    pub controller_and_externals: Map<int, ControllerAndExternalState>,
    pub network: NetworkState,
    pub rpc_id_allocator: RPCIdAllocator,
    pub req_drop_enabled: bool,
    pub pod_monkey_enabled: bool,
}

pub struct ControllerAndExternalState {
    pub controller: ControllerState,
    pub external: Option<ExternalState>,
    pub crash_enabled: bool,
}

impl ClusterState {

    #[verifier(inline)]
    pub open spec fn in_flight(self) -> Multiset<Message> {
        self.network.in_flight
    }

    #[verifier(inline)]
    pub open spec fn resources(self) -> StoredState {
        self.api_server.resources
    }

    #[verifier(inline)]
    pub open spec fn ongoing_reconciles(self, controller_id: int) -> Map<ObjectRef, OngoingReconcile> {
        self.controller_and_externals[controller_id].controller.ongoing_reconciles
    }

}


pub struct Cluster {
    pub installed_types: InstalledTypes,
    pub controller_models: Map<int, ControllerModel>,
}

pub struct ControllerModel {
    pub reconcile_model: ReconcileModel,
    pub external_model: Option<ExternalModel>,
}


// File: kubernetes_cluster/spec/message.rs
pub struct Message {
    pub src: HostId,
    pub dst: HostId,
    pub rpc_id: RPCId,
    pub content: MessageContent,
}

pub enum HostId {
    APIServer,
    BuiltinController,
    Controller(int, ObjectRef),
    External(int),
    PodMonkey,
}

pub struct RPCIdAllocator {
    pub rpc_id_counter: RPCId,
}

pub enum MessageContent {
    APIRequest(APIRequest),
    APIResponse(APIResponse),
    ExternalRequest(ExternalRequest),
    ExternalResponse(ExternalResponse),
}

pub open spec fn resp_msg_matches_req_msg(resp_msg: Message, req_msg: Message) -> bool {
    ||| {
        &&& resp_msg.content is APIResponse
        &&& req_msg.content is APIRequest
        &&& resp_msg.dst == req_msg.src
        &&& resp_msg.src == req_msg.dst
        &&& resp_msg.rpc_id == req_msg.rpc_id
        &&& match resp_msg.content.arrow_APIResponse_0() {
            APIResponse::GetResponse(_) => req_msg.content->APIRequest_0 is GetRequest,
            APIResponse::ListResponse(_) => req_msg.content->APIRequest_0 is ListRequest,
            APIResponse::CreateResponse(_) => req_msg.content->APIRequest_0 is CreateRequest,
            APIResponse::DeleteResponse(_) => req_msg.content->APIRequest_0 is DeleteRequest,
            APIResponse::UpdateResponse(_) => req_msg.content->APIRequest_0 is UpdateRequest,
            APIResponse::UpdateStatusResponse(_) => req_msg.content->APIRequest_0 is UpdateStatusRequest,
            APIResponse::GetThenDeleteResponse(_) => req_msg.content->APIRequest_0 is GetThenDeleteRequest,
            APIResponse::GetThenUpdateResponse(_) => req_msg.content->APIRequest_0 is GetThenUpdateRequest,
        }
    }
    ||| {
        &&& resp_msg.content is ExternalResponse
        &&& req_msg.content is ExternalRequest
        &&& resp_msg.dst == req_msg.src
        &&& resp_msg.src == req_msg.dst
        &&& resp_msg.rpc_id == req_msg.rpc_id
    }
}

macro_rules! declare_message_content_resp_helper_methods {
    ($is_fun:ident, $get_fun:ident, $resp_type:ty, $project:ident) => {
        verus! {
        impl MessageContent {
            pub open spec fn $is_fun(self) -> bool {
                &&& self is APIResponse
                &&& self.arrow_APIResponse_0() is $resp_type
            }

            pub open spec fn $get_fun(self) -> $resp_type {
                self.arrow_APIResponse_0().$project()
            }
        }
        }
    };
}


declare_message_content_resp_helper_methods!(
    is_list_response,
    get_list_response,
    ListResponse,
    arrow_ListResponse_0
);

// File: controllers/vreplicaset_controller/model/reconciler.rs
pub struct VReplicaSetReconcileState {
    pub reconcile_step: VReplicaSetRecStepView,
    pub filtered_pods: Option<Seq<PodView>>,
}

pub open spec fn objects_to_pods(objs: Seq<DynamicObjectView>) -> (pods_or_none: Option<Seq<PodView>>) {
    if objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() != 0 {
        None
    } else {
        Some(objs.map_values(|o: DynamicObjectView| PodView::unmarshal(o).unwrap()))
    }
}

pub open spec fn filter_pods(pods: Seq<PodView>, v_replica_set: VReplicaSetView) -> (filtered_pods: Seq<PodView>) {
    pods.filter(|pod: PodView|
        pod.metadata.owner_references_contains(v_replica_set.controller_owner_ref())
        && v_replica_set.spec.selector.matches(pod.metadata.labels.unwrap_or(Map::empty()))
        && pod.metadata.deletion_timestamp is None)
}


// File: controllers/vreplicaset_controller/trusted/spec_types.rs
pub struct VReplicaSetView {
    pub metadata: ObjectMetaView,
    pub spec: VReplicaSetSpecView,
    pub status: Option<VReplicaSetStatusView>,
}

implement_resource_view_trait!(VReplicaSetView, VReplicaSetSpecView, VReplicaSetSpecView::default(),
    Option<VReplicaSetStatusView>, None, VReplicaSetView::_kind(), _state_validation, _transition_validation);

impl VReplicaSetView {

    pub open spec fn controller_owner_ref(self) -> OwnerReferenceView {
        OwnerReferenceView {
            block_owner_deletion: Some(true),
            controller: Some(true),
            kind: Self::kind(),
            name: self.metadata.name->0,
            uid: self.metadata.uid->0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _kind() -> Kind { Kind::CustomResourceKind("vreplicaset"@) }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        // replicas is non-negative
        &&& self.spec.replicas is Some ==> self.spec.replicas->0 >= 0
        // selector exists, and its match_labels is not empty
        // TODO: revise it after supporting selector.match_expressions
        &&& self.spec.selector.match_labels is Some
        // labels are finite
        &&& self.spec.selector.match_labels->0.dom().finite()
        &&& self.spec.selector.match_labels->0.len() > 0
        // template, and its metadata ane spec exists
        &&& self.spec.template is Some
        &&& self.spec.template->0.metadata is Some
        &&& self.spec.template->0.spec is Some
        // kubernetes requires selector matches template's metadata's labels
        // and also requires selector to be non-empty, so it implicitly requires that the labels are non-empty
        &&& self.spec.template->0.metadata->0.labels is Some
        &&& self.spec.template->0.metadata->0.labels->0.dom().finite()
        &&& self.spec.selector.matches(self.spec.template->0.metadata->0.labels->0)
    }


}


pub struct VReplicaSetSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub template: Option<PodTemplateSpecView>,
}

impl VReplicaSetSpecView {

    pub open spec fn default() -> VReplicaSetSpecView {
        VReplicaSetSpecView {
            replicas: None,
            selector: LabelSelectorView::default(),
            template: None,
        }
    }

}


// File: controllers/vreplicaset_controller/trusted/step.rs
pub enum VReplicaSetRecStepView {
    Init,
    AfterListPods,
    AfterCreatePod(nat),
    AfterDeletePod(nat),
    Done,
    Error,
}


// File: kubernetes_api_objects/error.rs
#[derive(Debug)]
pub enum APIError {
    BadRequest,
    Conflict,
    Forbidden,
    Invalid,
    ObjectNotFound,
    ObjectAlreadyExists,
    NotSupported,
    InternalError,
    Timeout,
    ServerTimeout,
    TransactionAbort,
    Other
}

// File: kubernetes_cluster/proof/controller_runtime_liveness.rs
impl Cluster {

pub open spec fn pending_req_msg_is(controller_id: int, s: ClusterState, key: ObjectRef, req: Message) -> bool {
    s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(req)
}

}



// File: kubernetes_cluster/proof/objects_in_store.rs
impl Cluster {

pub open spec fn etcd_object_is_weakly_well_formed(key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[key];
        &&& obj.metadata.well_formed_for_namespaced()
        &&& obj.object_ref() == key
        &&& obj.metadata.resource_version->0 < s.api_server.resource_version_counter
        &&& obj.metadata.uid->0 < s.api_server.uid_counter
    }
}

pub open spec fn each_object_in_etcd_is_weakly_well_formed() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
                ==> Self::etcd_object_is_weakly_well_formed(key)(s)
    }
}

pub open spec fn etcd_is_finite() -> StatePred<ClusterState> {
    |s: ClusterState| s.resources().dom().finite()
}

}



// File: controllers/vreplicaset_controller/model/install.rs
impl Marshallable for VReplicaSetReconcileState {

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

}




// File: controllers/vreplicaset_controller/proof/predicate.rs
pub open spec fn at_vrs_step_with_vrs(vrs: VReplicaSetView, controller_id: int, step: VReplicaSetRecStepView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).unwrap();
        let local_state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
        &&& s.ongoing_reconciles(controller_id).contains_key(vrs.object_ref())
        &&& VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].triggering_cr).is_ok()
        &&& VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).is_ok()
        &&& triggering_cr.object_ref() == vrs.object_ref()
        &&& triggering_cr.spec() == vrs.spec()
        &&& triggering_cr.metadata().uid == vrs.metadata().uid
        &&& local_state.reconcile_step == step
    }
}

pub open spec fn resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(
    vrs: VReplicaSetView, controller_id: int, resp_msg: Message
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let step = VReplicaSetRecStepView::AfterListPods;
        let msg = s.ongoing_reconciles(controller_id)[vrs.object_ref()].pending_req_msg->0;
        &&& at_vrs_step_with_vrs(vrs, controller_id, step)(s)
        &&& Cluster::pending_req_msg_is(controller_id, s, vrs.object_ref(), msg)
        &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        &&& req_msg_is_list_pods_req(vrs, msg)
        &&& s.in_flight().contains(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, msg)
        &&& resp_msg_is_ok_list_resp_containing_matching_pods(s, vrs, resp_msg)
    }
}

pub open spec fn req_msg_is_list_pods_req(
    vrs: VReplicaSetView, req_msg: Message,
) -> bool {
    let request = req_msg.content.arrow_APIRequest_0();
    &&& req_msg.dst == HostId::APIServer
    &&& req_msg.content is APIRequest
    &&& request is ListRequest
    &&& request->ListRequest_0 == ListRequest {
        kind: PodView::kind(),
        namespace: vrs.metadata.namespace.unwrap(),
    }
}

pub open spec fn resp_msg_is_ok_list_resp_containing_matching_pods(
    s: ClusterState, vrs: VReplicaSetView, resp_msg: Message
) -> bool {
    let resp_objs = resp_msg.content.get_list_response().res.unwrap();
    let resp_obj_keys = resp_objs.map_values(|obj: DynamicObjectView| obj.object_ref());
    &&& resp_msg.content.is_list_response()
    &&& resp_msg.content.get_list_response().res is Ok
    &&& matching_pods(vrs, s.resources()) == resp_objs.filter(|obj| owned_selector_match_is(vrs, obj)).to_set()
    &&& objects_to_pods(resp_objs) is Some
    &&& objects_to_pods(resp_objs).unwrap().no_duplicates()
    &&& resp_objs.no_duplicates()
    &&& resp_obj_keys.no_duplicates()
    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj) is Ok
    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace is Some
    &&& forall |obj| resp_objs.contains(obj) ==> #[trigger] PodView::unmarshal(obj).unwrap().metadata.namespace == vrs.metadata.namespace
}


// File: controllers/vreplicaset_controller/trusted/liveness_theorem.rs
pub open spec fn matching_pods(vrs: VReplicaSetView, resources: StoredState) -> Set<DynamicObjectView> {
    resources.values().filter(|obj: DynamicObjectView| owned_selector_match_is(vrs, obj))
}

pub open spec fn owned_selector_match_is(vrs: VReplicaSetView, obj: DynamicObjectView) -> bool {
    &&& obj.kind == PodView::kind()
    &&& obj.metadata.namespace is Some
    &&& obj.metadata.namespace == vrs.metadata.namespace
    &&& obj.metadata.owner_references_contains(vrs.controller_owner_ref())
    &&& vrs.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
    &&& obj.metadata.deletion_timestamp is None
}

// File: controllers/vreplicaset_controller/proof/helper_lemmas.rs
pub proof fn lemma_filtered_pods_set_equals_matching_pods(
    s: ClusterState, vrs: VReplicaSetView, cluster: Cluster, 
    controller_id: int, resp_msg: Message
)
    requires
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        Cluster::etcd_is_finite()(s),
        resp_msg_is_the_in_flight_list_resp_at_after_list_pods_step(vrs, controller_id, resp_msg)(s),
        forall |obj: DynamicObjectView| #[trigger] matching_pods(vrs, s.resources()).contains(obj) ==> PodView::unmarshal(obj) is Ok,
    ensures
        ({
            let resp_objs = resp_msg.content.get_list_response().res.unwrap();
            let filtered_pods = filter_pods(objects_to_pods(resp_objs).unwrap(), vrs);
            let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
            &&& filtered_pods.no_duplicates()
            &&& filtered_pods.len() == matching_pods(vrs, s.resources()).len()
            &&& filtered_pods.to_set() == matching_pods(vrs, s.resources()).mk_map(|obj: DynamicObjectView| PodView::unmarshal(obj)->Ok_0).values()
            &&& filtered_pod_keys.no_duplicates()
        }),
{
}


}
