use vstd::prelude::*;
use vstd::math::abs;
use vstd::multiset::Multiset;

fn main() {}

verus!{

pub trait CustomResourceView : ResourceView {}

type RoleSpecView = Option<Seq<PolicyRuleView>>;

type RoleBindingSpecView = (RoleRefView, Option<Seq<SubjectView>>);

pub type ServiceStatusView = EmptyStatusView;

type ServiceAccountSpecView = Option<bool>;

pub type PodStatusView = EmptyStatusView;

type ConfigMapSpecView = Option<Map<StringView, StringView>>;

type SecretSpecView = Option<Map<StringView, StringView>>;

pub type PersistentVolumeClaimStatusView = EmptyStatusView;

pub type UnmarshalError = ();

/*
pub type PodMonkeyAction = Action<PodMonkeyState, PodMonkeyActionInput, PodMonkeyActionOutput>;
pub type PodMonkeyStateMachine = StateMachine<PodMonkeyState, PodMonkeyActionInput, PodMonkeyActionInput, PodMonkeyActionOutput, PodMonkeyStep>;
*/


pub type ActionPred<T> = spec_fn(T, T) -> bool;

pub type StatePred<T> = spec_fn(T) -> bool;
pub type VReplicaSetStatusView = EmptyStatusView;

pub type RPCId = nat;
pub type ExternalResponse = Value;

pub type ExternalRequest = Value;

pub type InstalledTypes = Map<StringView, InstalledType>;

pub type StringView = Seq<char>;

pub type ResourceVersion = int;

pub type Uid = int;

pub type Value = StringView;

pub type ExternalLocalState = Value;

pub type StoredState = Map<ObjectRef, DynamicObjectView>;

pub type EmptyStatusView = ();

pub type ReconcileLocalState = Value;

pub type ReconcileId = nat;


// File: kubernetes_api_objects/spec/resource.rs
pub trait Marshallable: Sized {

    spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

}

pub trait ResourceView: Sized {

    type Spec;

    type Status;

    spec fn metadata(self) -> ObjectMetaView;

    spec fn kind() -> Kind;

    spec fn object_ref(self) -> ObjectRef;

    spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError>;

    spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

    spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

    spec fn state_validation(self) -> bool;

}

pub open spec fn empty_status() -> EmptyStatusView {
    ()
}

macro_rules! implement_resource_view_trait {
    ($t:ty, $spec_t:ty, $spec_default:expr, $status_t:ty, $status_default:expr, $kind:expr, $state_validation:ident, $transition_validation:ident) => {
        verus! {

        impl ResourceView for $t {
            type Spec = $spec_t;
            type Status = $status_t;

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

            uninterp spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

            uninterp spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

            open spec fn state_validation(self) -> bool {
                self.$state_validation()
            }

        }

        }
    };
    ($t:ty, $spec_t:ty, $status_t:ty, $default:ident, $kind:expr, $spec:ident, $status:ident, $unmarshal:ident, $state_validation:ident, $transition_validation:ident) => {
        verus! {

        impl ResourceView for $t {
            type Spec = $spec_t;
            type Status = $status_t;

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

            open spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError> {
                if obj.kind != Self::kind() {
                    Err(())
                } else if !(Self::unmarshal_spec(obj.spec) is Ok) {
                    Err(())
                } else if !(Self::unmarshal_status(obj.status) is Ok) {
                    Err(())
                } else {
                    Ok(Self::$unmarshal(obj))
                }
            }

            uninterp spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

            uninterp spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

            open spec fn state_validation(self) -> bool {
                self.$state_validation()
            }

            }}}}


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
#[is_variant]
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

impl CreateRequest {

    pub open spec fn key(self) -> ObjectRef {
        ObjectRef {
            name: self.obj.metadata.name->0,
            namespace: self.namespace,
            kind: self.obj.kind,
        }
    }

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

#[is_variant]
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
#[is_variant]
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


// File: kubernetes_api_objects/spec/config_map.rs
pub struct ConfigMapView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>,
}

implement_resource_view_trait!(ConfigMapView, ConfigMapSpecView, EmptyStatusView, _default, Kind::ConfigMapKind, _spec,
    _status, _unmarshal_helper, _state_validation, _transition_validation);

impl ConfigMapView {

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> ConfigMapView {
        ConfigMapView {
            metadata: obj.metadata,
            data: ConfigMapView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool { true }

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


// File: kubernetes_api_objects/spec/daemon_set.rs
pub struct DaemonSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<DaemonSetSpecView>,
    pub status: Option<DaemonSetStatusView>,
}

implement_resource_view_trait!(DaemonSetView, Option<DaemonSetSpecView>, None, Option<DaemonSetStatusView>, None,
    Kind::DaemonSetKind, _state_validation, _transition_validation);

impl DaemonSetView {

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

}


pub struct DaemonSetSpecView {
    pub selector: LabelSelectorView,
    pub template: PodTemplateSpecView,
}

pub struct DaemonSetStatusView {
    pub number_ready: int,
}


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

    pub open spec fn matches(self, labels: Map<StringView, StringView>) -> bool {
        if self.match_labels is None {
            true
        } else {
            let match_labels = self.match_labels->0;
            forall |k, v| match_labels.contains_pair(k, v) ==> labels.contains_pair(k, v)
        }
    }

}



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


// File: kubernetes_api_objects/spec/persistent_volume_claim.rs
pub struct PersistentVolumeClaimView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PersistentVolumeClaimSpecView>,
    pub status: Option<PersistentVolumeClaimStatusView>,
}

implement_resource_view_trait!(PersistentVolumeClaimView, Option<PersistentVolumeClaimSpecView>, None,
    Option<PersistentVolumeClaimStatusView>, None, Kind::PersistentVolumeClaimKind, _state_validation,
    _transition_validation);

impl PersistentVolumeClaimView {

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

}


pub struct PersistentVolumeClaimSpecView {
    pub storage_class_name: Option<StringView>,
    pub access_modes: Option<Seq<StringView>>,
    pub resources: Option<VolumeResourceRequirementsView>,
}


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


// File: kubernetes_api_objects/spec/role.rs
pub struct RoleView {
    pub metadata: ObjectMetaView,
    pub policy_rules: Option<Seq<PolicyRuleView>>,
}

implement_resource_view_trait!(RoleView, RoleSpecView, EmptyStatusView, _default, Kind::RoleKind, _spec, _status,
    _unmarshal_helper, _state_validation, _transition_validation);

impl RoleView {

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> RoleView {
        RoleView {
            metadata: obj.metadata,
            policy_rules: RoleView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.policy_rules is Some
            ==> (forall |i| 0 <= i < self.policy_rules->0.len() ==> #[trigger] self.policy_rules->0[i].state_validation())
    }

}


pub struct PolicyRuleView {
    pub api_groups: Option<Seq<StringView>>,
    pub resources: Option<Seq<StringView>>,
    pub verbs: Seq<StringView>,
}

impl PolicyRuleView {

    pub open spec fn state_validation(self) -> bool {
        &&& self.api_groups is Some
        &&& self.api_groups->0.len() > 0
        &&& self.resources is Some
        &&& self.resources->0.len() > 0
        &&& self.verbs.len() > 0
    }

}



// File: kubernetes_api_objects/spec/role_binding.rs
pub struct RoleBindingView {
    pub metadata: ObjectMetaView,
    pub role_ref: RoleRefView,
    pub subjects: Option<Seq<SubjectView>>,
}

implement_resource_view_trait!(RoleBindingView, RoleBindingSpecView, EmptyStatusView, _default, Kind::RoleBindingKind,
    _spec, _status, _unmarshal_helper, _state_validation, _transition_validation);

impl RoleBindingView {

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> RoleBindingView {
        RoleBindingView {
            metadata: obj.metadata,
            role_ref: RoleBindingView::unmarshal_spec(obj.spec)->Ok_0.0,
            subjects: RoleBindingView::unmarshal_spec(obj.spec)->Ok_0.1,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        &&& self.role_ref.api_group == "rbac.authorization.k8s.io"@
        &&& (self.role_ref.kind == "Role"@ || self.role_ref.kind == "ClusterRole"@)
        // &&& self.role_ref.name.len() > 0
        // &&& self.subjects is Some
        //     ==> forall |i| 0 <= i < self.subjects->0.len() ==> #[trigger] self.subjects->0[i].state_validation(true)
    }

}


pub struct RoleRefView {
    pub api_group: StringView,
    pub kind: StringView,
    pub name: StringView,
}

pub struct SubjectView {
    pub kind: StringView,
    pub name: StringView,
    pub namespace: Option<StringView>,
}


// File: kubernetes_api_objects/spec/secret.rs
pub struct SecretView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>, // For view, <String, String> map is used instead of <String, Bytestring> map for now.
}

implement_resource_view_trait!(SecretView, SecretSpecView, EmptyStatusView, _default, Kind::SecretKind, _spec,
    _status, _unmarshal_helper, _state_validation, _transition_validation);

impl SecretView {

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> SecretView {
        SecretView {
            metadata: obj.metadata,
            data: SecretView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool { true }

}



// File: kubernetes_api_objects/spec/service.rs
pub struct ServiceView {
    pub metadata: ObjectMetaView,
    pub spec: Option<ServiceSpecView>,
    pub status: Option<ServiceStatusView>,
}

implement_resource_view_trait!(ServiceView, Option<ServiceSpecView>, None, Option<ServiceStatusView>, None,
    Kind::ServiceKind, _state_validation, _transition_validation);

impl ServiceView {

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

}


pub struct ServiceSpecView {
    pub cluster_ip: Option<StringView>,
    pub ports: Option<Seq<ServicePortView>>,
    pub selector: Option<Map<StringView, StringView>>,
    pub publish_not_ready_addresses: Option<bool>,
}

pub struct ServicePortView {
    pub name: Option<StringView>,
    pub port: int,
    pub app_protocol: Option<StringView>,
    pub protocol: Option<StringView>,
}


// File: kubernetes_api_objects/spec/service_account.rs
pub struct ServiceAccountView {
    pub metadata: ObjectMetaView,
    pub automount_service_account_token: Option<bool>,
}

implement_resource_view_trait!(ServiceAccountView, ServiceAccountSpecView, EmptyStatusView, _default,
    Kind::ServiceAccountKind, _spec, _status, _unmarshal_helper, _state_validation, _transition_validation);

impl ServiceAccountView {

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> ServiceAccountView {
        ServiceAccountView {
            metadata: obj.metadata,
            automount_service_account_token: ServiceAccountView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool { true }

}



// File: kubernetes_api_objects/spec/stateful_set.rs
pub struct StatefulSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<StatefulSetSpecView>,
    pub status: Option<StatefulSetStatusView>,
}

implement_resource_view_trait!(StatefulSetView, Option<StatefulSetSpecView>, None, Option<StatefulSetStatusView>, None,
    Kind::StatefulSetKind, _state_validation, _transition_validation);

impl StatefulSetView {

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        let new_spec = self.spec->0;
        &&& self.spec is Some
        &&& new_spec.replicas is Some ==> new_spec.replicas->0 >= 0
        // &&& new_spec.pod_management_policy is Some
        //     ==> (new_spec.pod_management_policy->0 == "OrderedReady"@
        //         || new_spec.pod_management_policy->0 == "Parallel"@)
        // &&& new_spec.persistent_volume_claim_retention_policy is Some
        //     ==> new_spec.persistent_volume_claim_retention_policy->0.state_validation()
    }

}


pub struct StatefulSetSpecView {
    pub min_ready_seconds: Option<int>,
    pub ordinals: Option<StatefulSetOrdinalsView>,
    pub persistent_volume_claim_retention_policy: Option<StatefulSetPersistentVolumeClaimRetentionPolicyView>,
    pub pod_management_policy: Option<StringView>,
    pub replicas: Option<int>,
    pub revision_history_limit: Option<int>,
    pub selector: LabelSelectorView,
    pub service_name: StringView,
    pub template: PodTemplateSpecView,
    pub update_strategy: Option<StatefulSetUpdateStrategyView>,
    pub volume_claim_templates: Option<Seq<PersistentVolumeClaimView>>,
}

pub struct StatefulSetPersistentVolumeClaimRetentionPolicyView {
    pub when_deleted: Option<StringView>,
    pub when_scaled: Option<StringView>,
}

pub struct StatefulSetOrdinalsView {
    pub start: Option<int>
}

pub struct StatefulSetUpdateStrategyView {
    pub type_: Option<StringView>,
    pub rolling_update: Option<RollingUpdateStatefulSetStrategyView>,
}

pub struct RollingUpdateStatefulSetStrategyView {
    pub partition: Option<int>,
    pub max_unavailable: Option<int>
}

pub struct StatefulSetStatusView {
    pub ready_replicas: Option<int>,
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


// File: kubernetes_api_objects/spec/volume_resource_requirements.rs
pub struct VolumeResourceRequirementsView {
    pub limits: Option<Map<StringView, StringView>>,
    pub requests: Option<Map<StringView, StringView>>,
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

    #[verifier(inline)]
    pub open spec fn scheduled_reconciles(self, controller_id: int) -> Map<ObjectRef, DynamicObjectView> {
        self.controller_and_externals[controller_id].controller.scheduled_reconciles
    }

    #[verifier(inline)]
    pub open spec fn reconcile_id_allocator(self, controller_id: int) -> ReconcileIdAllocator {
        self.controller_and_externals[controller_id].controller.reconcile_id_allocator
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

impl Cluster {

    #[verifier(inline)]
    pub open spec fn reconcile_model(self, controller_id: int) -> ReconcileModel {
        self.controller_models[controller_id].reconcile_model
    }

}



// File: kubernetes_cluster/spec/message.rs
pub struct Message {
    pub src: HostId,
    pub dst: HostId,
    pub rpc_id: RPCId,
    pub content: MessageContent,
}

#[is_variant]
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

#[is_variant]
pub enum MessageContent {
    APIRequest(APIRequest),
    APIResponse(APIResponse),
    ExternalRequest(ExternalRequest),
    ExternalResponse(ExternalResponse),
}

pub open spec fn is_ok_resp(resp: APIResponse) -> bool {
    match resp {
        APIResponse::GetResponse(get_resp) => get_resp.res is Ok,
        APIResponse::ListResponse(list_resp) => list_resp.res is Ok,
        APIResponse::CreateResponse(create_resp) => create_resp.res is Ok,
        APIResponse::DeleteResponse(delete_resp) => delete_resp.res is Ok,
        APIResponse::UpdateResponse(update_resp) => update_resp.res is Ok,
        APIResponse::UpdateStatusResponse(update_status_resp) => update_status_resp.res is Ok,
        APIResponse::GetThenDeleteResponse(resp) => resp.res is Ok,
        APIResponse::GetThenUpdateResponse(resp) => resp.res is Ok,
    }
}

pub open spec fn resp_msg_matches_req_msg(resp_msg: Message, req_msg: Message) -> bool {
    ||| {
        &&& resp_msg.content.is_APIResponse()
        &&& req_msg.content.is_APIRequest()
        &&& resp_msg.dst == req_msg.src
        &&& resp_msg.src == req_msg.dst
        &&& resp_msg.rpc_id == req_msg.rpc_id
        &&& match resp_msg.content.get_APIResponse_0() {
            APIResponse::GetResponse(_) => req_msg.content.get_APIRequest_0().is_GetRequest(),
            APIResponse::ListResponse(_) => req_msg.content.get_APIRequest_0().is_ListRequest(),
            APIResponse::CreateResponse(_) => req_msg.content.get_APIRequest_0().is_CreateRequest(),
            APIResponse::DeleteResponse(_) => req_msg.content.get_APIRequest_0().is_DeleteRequest(),
            APIResponse::UpdateResponse(_) => req_msg.content.get_APIRequest_0().is_UpdateRequest(),
            APIResponse::UpdateStatusResponse(_) => req_msg.content.get_APIRequest_0().is_UpdateStatusRequest(),
            APIResponse::GetThenDeleteResponse(_) => req_msg.content.get_APIRequest_0().is_GetThenDeleteRequest(),
            APIResponse::GetThenUpdateResponse(_) => req_msg.content.get_APIRequest_0().is_GetThenUpdateRequest(),
        }
    }
    ||| {
        &&& resp_msg.content.is_ExternalResponse()
        &&& req_msg.content.is_ExternalRequest()
        &&& resp_msg.dst == req_msg.src
        &&& resp_msg.src == req_msg.dst
        &&& resp_msg.rpc_id == req_msg.rpc_id
    }
}

impl HostId {

    pub open spec fn is_controller_id(self, controller_id: int) -> bool {
        match self {
            HostId::Controller(id, _) => id == controller_id,
            _ => false,
        }
    }

}

pub open spec fn form_msg(src: HostId, dst: HostId, rpc_id: RPCId, msg_content: MessageContent) -> Message {
    Message {
        src: src,
        dst: dst,
        rpc_id: rpc_id,
        content: msg_content,
    }
}


macro_rules! declare_message_content_req_helper_methods {
    ($is_fun:ident, $get_fun:ident, $req_type:ty, $project:ident) => {
        verus! {

        impl MessageContent {

            pub open spec fn $is_fun(self) -> bool {
                &&& self is APIRequest
                &&& self.get_APIRequest_0() is $req_type
            }

            pub open spec fn $get_fun(self) -> $req_type {
                self.get_APIRequest_0().$project()
            }
        }
        }
    };

}

declare_message_content_req_helper_methods!(
    is_get_request,
    get_get_request,
    GetRequest,
    get_GetRequest_0
);

declare_message_content_req_helper_methods!(
    is_list_request,
    get_list_request,
    ListRequest,
    get_ListRequest_0
);

declare_message_content_req_helper_methods!(
    is_create_request,
    get_create_request,
    CreateRequest,
    get_CreateRequest_0
);

declare_message_content_req_helper_methods!(
    is_delete_request,
    get_delete_request,
    DeleteRequest,
    get_DeleteRequest_0
);

declare_message_content_req_helper_methods!(
    is_update_status_request,
    get_update_status_request,
    UpdateStatusRequest,
    get_UpdateStatusRequest_0
);

declare_message_content_req_helper_methods!(
    is_update_request,
    get_update_request,
    UpdateRequest,
    get_UpdateRequest_0
);

declare_message_content_req_helper_methods!(
    is_get_then_delete_request,
    get_get_then_delete_request,
    GetThenDeleteRequest,
    get_GetThenDeleteRequest_0
);

declare_message_content_req_helper_methods!(
    is_get_then_update_request,
    get_get_then_update_request,
    GetThenUpdateRequest,
    get_GetThenUpdateRequest_0
);

macro_rules! declare_message_content_resp_helper_methods {
    ($is_fun:ident, $get_fun:ident, $resp_type:ty, $project:ident) => {
        verus! {
        impl MessageContent {
            pub open spec fn $is_fun(self) -> bool {
                &&& self is APIResponse
                &&& self.get_APIResponse_0() is $resp_type
            }

            pub open spec fn $get_fun(self) -> $resp_type {
                self.get_APIResponse_0().$project()
            }
        }
        }
    };
}

declare_message_content_resp_helper_methods!(
    is_get_then_delete_response,
    get_get_then_delete_response,
    GetThenDeleteResponse,
    get_GetThenDeleteResponse_0
);


declare_message_content_resp_helper_methods!(
    is_create_response,
    get_create_response,
    CreateResponse,
    get_CreateResponse_0
);


declare_message_content_resp_helper_methods!(
    is_update_status_response,
    get_update_status_response,
    UpdateStatusResponse,
    get_UpdateStatusResponse_0
);

declare_message_content_resp_helper_methods!(
    is_list_response,
    get_list_response,
    ListResponse,
    get_ListResponse_0
);

macro_rules! declare_form_resp_msg_functions {
    ($fun:ident, $resp_type:ty) => {
        verus! {
        pub open spec fn $fun(req_msg: Message, resp: $resp_type) -> Message {
            form_msg(req_msg.dst, req_msg.src, req_msg.rpc_id, MessageContent::APIResponse(APIResponse::$resp_type(resp)))
        }
        }
    };
}

declare_form_resp_msg_functions!(form_get_resp_msg, GetResponse);

declare_form_resp_msg_functions!(form_list_resp_msg, ListResponse);

declare_form_resp_msg_functions!(form_create_resp_msg, CreateResponse);

declare_form_resp_msg_functions!(form_delete_resp_msg, DeleteResponse);

declare_form_resp_msg_functions!(form_update_resp_msg, UpdateResponse);

declare_form_resp_msg_functions!(form_update_status_resp_msg, UpdateStatusResponse);

declare_form_resp_msg_functions!(form_get_then_delete_resp_msg, GetThenDeleteResponse);

declare_form_resp_msg_functions!(form_get_then_update_resp_msg, GetThenUpdateResponse);

// File: controllers/vreplicaset_controller/model/reconciler.rs
pub struct VReplicaSetReconcileState {
    pub reconcile_step: VReplicaSetRecStepView,
    pub filtered_pods: Option<Seq<PodView>>,
}


// File: controllers/vreplicaset_controller/trusted/spec_types.rs
pub struct VReplicaSetView {
    pub metadata: ObjectMetaView,
    pub spec: VReplicaSetSpecView,
    pub status: Option<VReplicaSetStatusView>,
}

impl CustomResourceView for VReplicaSetView {}

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


// File: controllers/vreplicaset_controller/trusted/step.rs
#[is_variant]
pub enum VReplicaSetRecStepView {
    Init,
    AfterListPods,
    AfterCreatePod(nat),
    AfterDeletePod(nat),
    Done,
    Error,
}


// File: kubernetes_api_objects/error.rs
#[is_variant]
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


// File: temporal_logic/defs.rs
pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
}

impl<T> Execution<T> {

    pub open spec fn head(self) -> T {
        (self.nat_to_state)(0)
    }

    pub open spec fn suffix(self, pos: nat) -> Self {
        Execution {
            nat_to_state: |i: nat| (self.nat_to_state)(i + pos),
        }
    }

}


#[verifier(reject_recursive_types(T))]
pub struct TempPred<T> {
    pub pred: spec_fn(Execution<T>) -> bool,
}

impl<T> TempPred<T> {

    pub open spec fn new(pred: spec_fn(Execution<T>) -> bool) -> Self {
        TempPred {
            pred: pred,
        }
    }

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        (self.pred)(execution)
    }

    pub open spec fn and(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) && other.satisfied_by(ex))
    }

    pub open spec fn implies(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
    }

}


pub open spec fn lift_state<T>(state_pred: StatePred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| state_pred(ex.head()))
}

pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn tla_forall<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |a: A| #[trigger] a_to_temp_pred(a).satisfied_by(ex))
}

pub open spec fn stable<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred.implies(always(temp_pred)).satisfied_by(ex))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: kubernetes_cluster/spec/api_server/state_machine.rs
#[verifier(inline)]
pub open spec fn unmarshallable_spec(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal_spec(obj.spec) is Ok,
        Kind::DaemonSetKind => DaemonSetView::unmarshal_spec(obj.spec) is Ok,
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal_spec(obj.spec) is Ok,
        Kind::PodKind => PodView::unmarshal_spec(obj.spec) is Ok,
        Kind::RoleBindingKind => RoleBindingView::unmarshal_spec(obj.spec) is Ok,
        Kind::RoleKind => RoleView::unmarshal_spec(obj.spec) is Ok,
        Kind::SecretKind => SecretView::unmarshal_spec(obj.spec) is Ok,
        Kind::ServiceKind => ServiceView::unmarshal_spec(obj.spec) is Ok,
        Kind::StatefulSetKind => StatefulSetView::unmarshal_spec(obj.spec) is Ok,
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal_spec(obj.spec) is Ok,
        Kind::CustomResourceKind(string) => (installed_types[string].unmarshallable_spec)(obj.spec),
    }
}

#[verifier(inline)]
pub open spec fn unmarshallable_status(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal_status(obj.status) is Ok,
        Kind::DaemonSetKind => DaemonSetView::unmarshal_status(obj.status) is Ok,
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal_status(obj.status) is Ok,
        Kind::PodKind => PodView::unmarshal_status(obj.status) is Ok,
        Kind::RoleBindingKind => RoleBindingView::unmarshal_status(obj.status) is Ok,
        Kind::RoleKind => RoleView::unmarshal_status(obj.status) is Ok,
        Kind::SecretKind => SecretView::unmarshal_status(obj.status) is Ok,
        Kind::ServiceKind => ServiceView::unmarshal_status(obj.status) is Ok,
        Kind::StatefulSetKind => StatefulSetView::unmarshal_status(obj.status) is Ok,
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal_status(obj.status) is Ok,
        Kind::CustomResourceKind(string) => (installed_types[string].unmarshallable_status)(obj.status),
    }
}

pub open spec fn unmarshallable_object(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    unmarshallable_spec(obj, installed_types) && unmarshallable_status(obj, installed_types)
}

pub open spec fn valid_object(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::DaemonSetKind => DaemonSetView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::PodKind => PodView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::RoleBindingKind => RoleBindingView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::RoleKind => RoleView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::SecretKind => SecretView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::ServiceKind => ServiceView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::StatefulSetKind => StatefulSetView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::CustomResourceKind(string) => (installed_types[string].valid_object)(obj),
    }
}


// File: controllers/vreplicaset_controller/proof/helper_invariants/predicate.rs
pub open spec fn vrs_reconcile_create_request_only_interferes_with_itself(
    req: CreateRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let owner_references = req.obj.metadata.owner_references->0;
        &&& req.obj.kind == Kind::PodKind
        &&& req.key().namespace == vrs.metadata.namespace.unwrap()
        &&& req.obj.metadata.owner_references is Some
        &&& exists |owner_ref: OwnerReferenceView| {
            // using the macro messes up the trigger.
            &&& owner_references == #[trigger] Seq::empty().push(owner_ref)
            &&& owner_ref.controller is Some
            &&& owner_ref.controller->0
            &&& owner_ref.kind == VReplicaSetView::kind()
            &&& owner_ref.name == vrs.object_ref().name
        }
    }
}

pub open spec fn vrs_reconcile_get_then_delete_request_only_interferes_with_itself(
    req: GetThenDeleteRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& req.key.kind == Kind::PodKind
        &&& req.key.namespace == vrs.metadata.namespace.unwrap()
        &&& req.owner_ref.controller is Some
        &&& req.owner_ref.controller->0
        &&& req.owner_ref.kind == VReplicaSetView::kind()
        &&& req.owner_ref.name == vrs.object_ref().name
    }
}

pub open spec fn vrs_reconcile_request_only_interferes_with_itself(
    controller_id: int,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src == HostId::Controller(controller_id, vrs.object_ref())
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::ListRequest(_) => true,
            APIRequest::CreateRequest(req) => vrs_reconcile_create_request_only_interferes_with_itself(req, vrs)(s),
            APIRequest::GetThenDeleteRequest(req) => vrs_reconcile_get_then_delete_request_only_interferes_with_itself(req, vrs)(s),
            _ => false, // vrs doesn't send other requests (yet).
        }
    }
}

pub open spec fn each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> {
                // Unlike the below invariant, this entire invariant is used in both proving itself as well as in other proofs.
                let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                let triggering_cr = VReplicaSetView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                let filtered_pods = state.filtered_pods.unwrap();
                &&& triggering_cr.object_ref() == key
                &&& triggering_cr.metadata().well_formed_for_namespaced()
                &&& state.filtered_pods is Some ==>
                // Maintained across deletes, 
                // maintained across creates since all new keys with generate_name
                // are unique, maintained across updates since there are
                // no updates.
                    forall |i| #![trigger filtered_pods[i]] 0 <= i < filtered_pods.len() ==>
                    (
                        filtered_pods[i].object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                        && ((s.resources().contains_key(filtered_pods[i].object_ref())
                                && s.resources()[filtered_pods[i].object_ref()].metadata.resource_version
                                    == filtered_pods[i].metadata.resource_version) ==>
                            (s.resources()[filtered_pods[i].object_ref()].metadata.owner_references_contains(
                                triggering_cr.controller_owner_ref()
                                )
                             ))
                        && filtered_pods[i].metadata.resource_version.is_some()
                        && filtered_pods[i].metadata.resource_version.unwrap()
                            < s.api_server.resource_version_counter
                    )
                // Special case: the above property holds on a list response to the
                // appropriate request. 
                &&& state.reconcile_step.is_AfterListPods() ==> {
                    let req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                    &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                    &&& req_msg.dst.is_APIServer()
                    &&& req_msg.content.is_list_request()
                    &&& req_msg.content.get_list_request() == ListRequest {
                        kind: PodView::kind(),
                        namespace: triggering_cr.metadata.namespace.unwrap(),
                    }
                    &&& forall |msg| {
                        let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg->0;
                        &&& #[trigger] s.in_flight().contains(msg)
                        &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                        &&& msg.src.is_APIServer()
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                        &&& is_ok_resp(msg.content.get_APIResponse_0())
                    } ==> {
                        let resp_objs = msg.content.get_list_response().res.unwrap();
                        &&& msg.content.is_list_response()
                        &&& msg.content.get_list_response().res is Ok
                        &&& resp_objs.filter(|o: DynamicObjectView| PodView::unmarshal(o).is_err()).len() == 0 
                        &&& forall |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len() ==>
                        (
                            resp_objs[i].metadata.namespace.is_some()
                            && resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                            && ((s.resources().contains_key(resp_objs[i].object_ref())
                                    && s.resources()[resp_objs[i].object_ref()].metadata.resource_version
                                    == resp_objs[i].metadata.resource_version) ==> 
                                    s.resources()[resp_objs[i].object_ref()].metadata
                                        == resp_objs[i].metadata)
                            && resp_objs[i].metadata.resource_version.is_some()
                            && resp_objs[i].metadata.resource_version.unwrap()
                                    < s.api_server.resource_version_counter
                        )
                    }
                }
            }
    }
}

pub open spec fn every_msg_from_vrs_controller_carries_vrs_key(
    controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            let content = msg.content;
            &&& s.in_flight().contains(msg)
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
        } ==> {
            msg.src.get_Controller_1().kind == VReplicaSetView::kind()
        }
    }
}

// File: kubernetes_cluster/proof/cluster.rs
impl Cluster {

pub open spec fn there_is_the_controller_state(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| s.controller_and_externals.contains_key(controller_id)
}

}



// File: kubernetes_cluster/proof/controller_runtime_liveness.rs
impl Cluster {

pub open spec fn has_pending_req_msg(controller_id: int, s: ClusterState, key: ObjectRef) -> bool {
    &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
    &&& (s.ongoing_reconciles(controller_id)[key].pending_req_msg->0.content.is_APIRequest()
        || s.ongoing_reconciles(controller_id)[key].pending_req_msg->0.content.is_ExternalRequest())
}

pub open spec fn no_pending_req_msg(controller_id: int, s: ClusterState, key: ObjectRef) -> bool {
    s.ongoing_reconciles(controller_id)[key].pending_req_msg is None
}

pub open spec fn request_sent_by_controller_with_key(controller_id: int, key: ObjectRef, msg: Message) -> bool {
    &&& msg.src == HostId::Controller(controller_id, key)
    &&& {
        ||| {
            &&& msg.dst == HostId::APIServer
            &&& msg.content.is_APIRequest()
        }
        ||| {
            &&& msg.dst == HostId::External(controller_id)
            &&& msg.content.is_ExternalRequest()
        }
    }
}

pub open spec fn at_expected_reconcile_states(controller_id: int, key: ObjectRef, expected_states: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
        &&& expected_states(s.ongoing_reconciles(controller_id)[key].local_state)
    }
}

pub open spec fn no_pending_req_msg_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
            ==> Self::no_pending_req_msg(controller_id, s, key)
    }
}

pub open spec fn pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
        ==> {
            let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            &&& Self::has_pending_req_msg(controller_id, s, key)
            &&& Self::request_sent_by_controller_with_key(controller_id, key, msg)
            &&& (s.in_flight().contains(msg)
                || exists |resp_msg: Message| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                })
        }
    }
}

pub open spec fn there_is_no_request_msg_to_external_from_controller(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg) // not the ideal trigger choice, but no matches for the second conjunct anymore.
            && msg.src.is_controller_id(controller_id)
            ==> msg.dst != HostId::External(controller_id)
    }
}

}



// File: kubernetes_cluster/proof/controller_runtime_safety.rs
impl Cluster {

pub open spec fn cr_objects_in_schedule_satisfy_state_validation<T: CustomResourceView>(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            let unmarshal_result =
                T::unmarshal(s.scheduled_reconciles(controller_id)[key]);
            #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
            && key.kind.is_CustomResourceKind()
            && key.kind == T::kind()
            ==> unmarshal_result is Ok
                && unmarshal_result.unwrap().state_validation()
        }
    }
}

pub open spec fn cr_objects_in_reconcile_satisfy_state_validation<T: CustomResourceView>(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            let unmarshal_result =
                T::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr);
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            && key.kind.is_CustomResourceKind()
            && key.kind == T::kind()
            ==> unmarshal_result is Ok
                && unmarshal_result.unwrap().state_validation()
        }
    }
}

pub open spec fn cr_states_are_unmarshallable<S: Marshallable, K: CustomResourceView>(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            let unmarshal_result =
                S::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state);
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            && key.kind.is_CustomResourceKind()
            && key.kind == K::kind()
            ==> unmarshal_result is Ok
        }
    }
}

pub open spec fn cr_objects_in_reconcile_have_correct_kind<T: CustomResourceView>(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> key.kind == T::kind()
        }
    }
}

pub open spec fn ongoing_reconciles_is_finite(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.ongoing_reconciles(controller_id).dom().finite()
    }
}

pub open spec fn every_ongoing_reconcile_has_lower_id_than_allocator(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> s.ongoing_reconciles(controller_id)[key].reconcile_id
                    < s.reconcile_id_allocator(controller_id).reconcile_id_counter
    }
}

}



// File: kubernetes_cluster/proof/network.rs
impl Cluster {

pub open spec fn every_in_flight_msg_has_lower_id_than_allocator() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg)
            ==> msg.rpc_id < s.rpc_id_allocator.rpc_id_counter
    }
}

pub open spec fn pending_req_of_key_is_unique_with_unique_id(controller_id: int, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.ongoing_reconciles(controller_id).contains_key(key)
        && s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
        ==> (
            forall |other_key: ObjectRef|
                #[trigger] s.ongoing_reconciles(controller_id).contains_key(other_key)
                && key != other_key
                && s.ongoing_reconciles(controller_id)[other_key].pending_req_msg is Some
                ==> s.ongoing_reconciles(controller_id)[key].pending_req_msg->0.rpc_id
                    != s.ongoing_reconciles(controller_id)[other_key].pending_req_msg->0.rpc_id
        )
    }
}

pub open spec fn every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef| {
            let pending_req = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            && s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
            ==> {
                forall |msg: Message|
                    #[trigger] s.in_flight().contains(msg)
                    && msg.content.is_APIRequest()
                    && msg != pending_req
                    ==> msg.rpc_id != pending_req.rpc_id
            }
        }
    }
}

pub open spec fn every_in_flight_req_msg_from_controller_has_valid_controller_id(self) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg)
            && msg.content.is_APIRequest()
            && msg.src.is_Controller()
            ==> self.controller_models.contains_key(msg.src.get_Controller_0())
    }
}

pub open spec fn every_in_flight_msg_has_no_replicas_and_has_unique_id() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg|
            #[trigger] s.in_flight().contains(msg)
            ==> s.in_flight().count(msg) == 1
                && (
                    forall |other_msg|
                        #[trigger] s.in_flight().contains(other_msg)
                        && msg != other_msg
                        ==> msg.rpc_id != other_msg.rpc_id
                )
    }
}

pub open spec fn every_in_flight_msg_has_unique_id() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg1, msg2|
            #[trigger] s.in_flight().contains(msg1)
            && #[trigger] s.in_flight().contains(msg2)
            && msg1 != msg2
            ==>  msg1.rpc_id != msg2.rpc_id
    }
}

}



// File: kubernetes_cluster/proof/objects_in_reconcile.rs
impl Cluster {

pub open spec fn each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
                ==> s.scheduled_reconciles(controller_id)[key].object_ref() == key
                    && s.scheduled_reconciles(controller_id)[key].metadata.well_formed_for_namespaced()
    }
}

pub open spec fn each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
                ==> s.ongoing_reconciles(controller_id)[key].triggering_cr.object_ref() == key
                    && s.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.well_formed_for_namespaced()
    }
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

pub open spec fn etcd_object_is_well_formed(self, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[key];
        &&& Self::etcd_object_is_weakly_well_formed(key)(s)
        &&& unmarshallable_object(obj, self.installed_types)
        &&& valid_object(obj, self.installed_types)
    }
}

pub open spec fn each_builtin_object_in_etcd_is_well_formed(self) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
            && !key.kind.is_CustomResourceKind()
                ==> self.etcd_object_is_well_formed(key)(s)
    }
}

pub open spec fn each_custom_object_in_etcd_is_well_formed<T: CustomResourceView>(self) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
            && key.kind == T::kind()
                ==> self.etcd_object_is_well_formed(key)(s)
    }
}

pub open spec fn each_object_in_etcd_has_at_most_one_controller_owner() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
                ==> {
                    let obj = s.resources()[key];
                    let owners = obj.metadata.owner_references->0;
                    let controller_owners = owners.filter(
                        |o: OwnerReferenceView| o.controller is Some && o.controller->0
                    );
                    obj.metadata.owner_references is Some ==> controller_owners.len() <= 1
                }
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
pub open spec fn at_step_closure(step: VReplicaSetRecStepView) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| VReplicaSetReconcileState::unmarshal(s).unwrap().reconcile_step == step
}

pub open spec fn unwrap_local_state_closure<T>(
    closure: spec_fn(VReplicaSetReconcileState) -> T
) -> spec_fn(ReconcileLocalState) -> T {
    |s: ReconcileLocalState| closure(VReplicaSetReconcileState::unmarshal(s).unwrap())
}


// File: temporal_logic/rules.rs
	#[verifier::external_body]
pub proof fn always_p_is_stable<T>(p: TempPred<T>)
    ensures valid(stable(always(p))),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn stable_and_temp<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        valid(stable(p)),
        valid(stable(q)),
    ensures valid(stable(p.and(q))),
	{
		unimplemented!()
	}

#[macro_export]
macro_rules! stable_and_n {
    [$($tail:tt)*] => {
        verus_proof_macro_exprs!(stable_and_n_internal!($($tail)*));
    };
}

#[macro_export]
macro_rules! stable_and_n_internal {
    ($p1:expr, $p2:expr) => {
        stable_and_temp($p1, $p2);
    };
    ($p1:expr, $p2:expr, $($tail:tt)*) => {
        stable_and_temp($p1, $p2);
        stable_and_n_internal!($p1.and($p2), $($tail)*);
    };
}


// File: controllers/vreplicaset_controller/proof/liveness/spec.rs
pub open spec fn derived_invariants_since_beginning(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(Cluster::every_in_flight_msg_has_unique_id()))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_lower_id_than_allocator())))
    .and(always(lift_state(Cluster::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of_every_ongoing_reconcile(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())))
    .and(always(lift_state(cluster.each_builtin_object_in_etcd_is_well_formed())))
    .and(always(lift_state(cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>())))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<VReplicaSetView>(controller_id))))
    .and(always(lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id())))
    .and(always(lift_state(Cluster::every_in_flight_msg_has_no_replicas_and_has_unique_id())))
    .and(always(lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner())))
    .and(always(lift_state(Cluster::cr_objects_in_schedule_satisfy_state_validation::<VReplicaSetView>(controller_id))))
    .and(always(lift_state(Cluster::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id))))
    .and(always(lift_state(Cluster::every_ongoing_reconcile_has_lower_id_than_allocator(controller_id))))
    .and(always(lift_state(Cluster::ongoing_reconciles_is_finite(controller_id))))
    .and(always(lift_state(Cluster::cr_objects_in_reconcile_have_correct_kind::<VReplicaSetView>(controller_id))))
    .and(always(lift_state(Cluster::etcd_is_finite())))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_of_key_is_unique_with_unique_id(controller_id, vrs.object_ref())))))
    .and(always(lift_state(Cluster::there_is_the_controller_state(controller_id))))
    .and(always(lift_state(Cluster::there_is_no_request_msg_to_external_from_controller(controller_id))))
    .and(always(lift_state(Cluster::cr_states_are_unmarshallable::<VReplicaSetReconcileState, VReplicaSetView>(controller_id))))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::no_pending_req_msg_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::Init))))))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), at_step_closure(VReplicaSetRecStepView::AfterListPods))))))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterCreatePod()
    ))))))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id, vrs.object_ref(), unwrap_local_state_closure(
        |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
    ))))))
    .and(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id,
        vrs.object_ref(),
        cluster.reconcile_model(controller_id).done
    ))))
    .and(always(lift_state(Cluster::no_pending_req_msg_at_reconcile_state(
        controller_id,
        vrs.object_ref(),
        cluster.reconcile_model(controller_id).error
    ))))
    .and(always(tla_forall(|vrs: VReplicaSetView| lift_state(vrs_reconcile_request_only_interferes_with_itself(controller_id, vrs)))))
    .and(always(lift_state(each_vrs_in_reconcile_implies_filtered_pods_owned_by_vrs(controller_id))))
    .and(always(lift_state(every_msg_from_vrs_controller_carries_vrs_key(controller_id))))
}

pub proof fn derived_invariants_since_beginning_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(derived_invariants_since_beginning(vrs, cluster, controller_id))),
{
}



}
