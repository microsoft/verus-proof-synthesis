use vstd::prelude::*;
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
pub type EmptyStatusView = ();

// File: kubernetes_api_objects/spec/resource.rs
pub trait ResourceView: Sized {

    type Spec;

    type Status;

    spec fn default() -> Self;

    spec fn metadata(self) -> ObjectMetaView;

    spec fn kind() -> Kind;

    spec fn spec(self) -> Self::Spec;

    spec fn status(self) -> Self::Status;

    spec fn marshal(self) -> DynamicObjectView;

    spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError>;

    spec fn marshal_spec(s: Self::Spec) -> Value;

    spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

    spec fn marshal_status(s: Self::Status) -> Value;

    spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

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

            uninterp spec fn marshal_spec(s: Self::Spec) -> Value;

            uninterp spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

            uninterp spec fn marshal_status(s: Self::Status) -> Value;

            uninterp spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

            open spec fn state_validation(self) -> bool {
                self.$state_validation()
            }

}}}}



// File: kubernetes_api_objects/exec/api_method.rs
pub enum KubeAPIRequest {
    GetRequest(KubeGetRequest),
    ListRequest(KubeListRequest),
    CreateRequest(KubeCreateRequest),
    DeleteRequest(KubeDeleteRequest),
    UpdateRequest(KubeUpdateRequest),
    UpdateStatusRequest(KubeUpdateStatusRequest),
    GetThenDeleteRequest(KubeGetThenDeleteRequest),
    GetThenUpdateRequest(KubeGetThenUpdateRequest),
}

pub struct KubeGetRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
}

impl View for KubeGetRequest {

    type V = GetRequest;

    open spec fn view(&self) -> GetRequest {
        GetRequest {
            key: ObjectRef {
                kind: self.api_resource@.kind,
                name: self.name@,
                namespace: self.namespace@,
            },
        }
    }

}


pub struct KubeListRequest {
    pub api_resource: ApiResource,
    pub namespace: String,
}

impl View for KubeListRequest {

    type V = ListRequest;

    open spec fn view(&self) -> ListRequest {
        ListRequest {
            kind: self.api_resource@.kind,
            namespace: self.namespace@,
        }
    }

}


pub struct KubeCreateRequest {
    pub api_resource: ApiResource,
    pub namespace: String,
    pub obj: DynamicObject,
}

impl View for KubeCreateRequest {

    type V = CreateRequest;

    open spec fn view(&self) -> CreateRequest {
        CreateRequest {
            namespace: self.namespace@,
            obj: self.obj@,
        }
    }

}


pub struct KubeDeleteRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub preconditions: Option<Preconditions>,
}

impl View for KubeDeleteRequest {

    type V = DeleteRequest;

    open spec fn view(&self) -> DeleteRequest {
        DeleteRequest {
            key: ObjectRef {
                kind: self.api_resource@.kind,
                name: self.name@,
                namespace: self.namespace@,
            },
            preconditions: self.preconditions.deep_view(),
        }
    }

}


pub struct KubeUpdateRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub obj: DynamicObject,
}

impl View for KubeUpdateRequest {

    type V = UpdateRequest;

    open spec fn view(&self) -> UpdateRequest {
        UpdateRequest {
            name: self.name@,
            namespace: self.namespace@,
            obj: self.obj@,
        }
    }

}


pub struct KubeUpdateStatusRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub obj: DynamicObject,
}

impl View for KubeUpdateStatusRequest {

    type V = UpdateStatusRequest;

    open spec fn view(&self) -> UpdateStatusRequest {
        UpdateStatusRequest {
            name: self.name@,
            namespace: self.namespace@,
            obj: self.obj@,
        }
    }

}


pub struct KubeGetThenDeleteRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub owner_ref: OwnerReference,
}

impl View for KubeGetThenDeleteRequest {

    type V = GetThenDeleteRequest;

    open spec fn view(&self) -> GetThenDeleteRequest {
        GetThenDeleteRequest {
            key: ObjectRef {
                kind: self.api_resource@.kind,
                name: self.name@,
                namespace: self.namespace@,
            },
            owner_ref: self.owner_ref@,
        }
    }

}


pub struct KubeGetThenUpdateRequest {
    pub api_resource: ApiResource,
    pub name: String,
    pub namespace: String,
    pub owner_ref: OwnerReference,
    pub obj: DynamicObject,
}

impl View for KubeGetThenUpdateRequest {

    type V = GetThenUpdateRequest;

    open spec fn view(&self) -> GetThenUpdateRequest {
        GetThenUpdateRequest {
            name: self.name@,
            namespace: self.namespace@,
            owner_ref: self.owner_ref@,
            obj: self.obj@,
        }
    }

}


impl View for KubeAPIRequest {

    type V = APIRequest;

    open spec fn view(&self) -> APIRequest {
        match self {
            KubeAPIRequest::GetRequest(get_req) => APIRequest::GetRequest(get_req@),
            KubeAPIRequest::ListRequest(list_req) => APIRequest::ListRequest(list_req@),
            KubeAPIRequest::CreateRequest(create_req) => APIRequest::CreateRequest(create_req@),
            KubeAPIRequest::DeleteRequest(delete_req) => APIRequest::DeleteRequest(delete_req@),
            KubeAPIRequest::UpdateRequest(update_req) => APIRequest::UpdateRequest(update_req@),
            KubeAPIRequest::UpdateStatusRequest(update_status_req) => APIRequest::UpdateStatusRequest(update_status_req@),
            KubeAPIRequest::GetThenDeleteRequest(req) => APIRequest::GetThenDeleteRequest(req@),
            KubeAPIRequest::GetThenUpdateRequest(req) => APIRequest::GetThenUpdateRequest(req@),
        }
    }

}


impl DeepView for KubeAPIRequest {

    type V = APIRequest;

    open spec fn deep_view(&self) -> APIRequest {
        self@
    }

}


pub enum KubeAPIResponse {
    GetResponse(KubeGetResponse),
    ListResponse(KubeListResponse),
    CreateResponse(KubeCreateResponse),
    DeleteResponse(KubeDeleteResponse),
    UpdateResponse(KubeUpdateResponse),
    UpdateStatusResponse(KubeUpdateStatusResponse),
    GetThenDeleteResponse(KubeGetThenDeleteResponse),
    GetThenUpdateResponse(KubeGetThenUpdateResponse),
}

pub struct KubeGetResponse {
    pub res: Result<DynamicObject, APIError>,
}

impl View for KubeGetResponse {

    type V = GetResponse;

    open spec fn view(&self) -> GetResponse {
        match self.res {
            Ok(o) => GetResponse { res: Ok(o@) },
            Err(e) => GetResponse { res: Err(e) },
        }
    }

}


pub struct KubeListResponse {
    pub res: Result<Vec<DynamicObject>, APIError>,
}

impl View for KubeListResponse {

    type V = ListResponse;

    open spec fn view(&self) -> ListResponse {
        match self.res {
            Ok(l) => ListResponse { res: Ok(l.deep_view()) },
            Err(e) => ListResponse { res: Err(e) },
        }
    }

}


pub struct KubeCreateResponse {
    pub res: Result<DynamicObject, APIError>,
}

impl View for KubeCreateResponse {

    type V = CreateResponse;

    open spec fn view(&self) -> CreateResponse {
        match self.res {
            Ok(o) => CreateResponse { res: Ok(o@) },
            Err(e) => CreateResponse { res: Err(e) },
        }
    }

}


pub struct KubeDeleteResponse {
    pub res: Result<(), APIError>,
}

impl View for KubeDeleteResponse {

    type V = DeleteResponse;

    open spec fn view(&self) -> DeleteResponse {
        match self.res {
            Ok(_) => DeleteResponse { res: Ok(()) },
            Err(e) => DeleteResponse { res: Err(e) },
        }
    }

}


pub struct KubeUpdateResponse {
    pub res: Result<DynamicObject, APIError>,
}

impl View for KubeUpdateResponse {

    type V = UpdateResponse;

    open spec fn view(&self) -> UpdateResponse {
        match self.res {
            Ok(o) => UpdateResponse { res: Ok(o@) },
            Err(e) => UpdateResponse { res: Err(e) },
        }
    }

}


pub struct KubeUpdateStatusResponse {
    pub res: Result<DynamicObject, APIError>,
}

impl View for KubeUpdateStatusResponse {

    type V = UpdateStatusResponse;

    open spec fn view(&self) -> UpdateStatusResponse {
        match self.res {
            Ok(o) => UpdateStatusResponse { res: Ok(o@) },
            Err(e) => UpdateStatusResponse { res: Err(e) },
        }
    }

}


pub struct KubeGetThenUpdateResponse {
    pub res: Result<DynamicObject, APIError>,
}

impl View for KubeGetThenUpdateResponse {

    type V = GetThenUpdateResponse;

    open spec fn view(&self) -> GetThenUpdateResponse {
        match self.res {
            Ok(o) => GetThenUpdateResponse { res: Ok(o@) },
            Err(e) => GetThenUpdateResponse { res: Err(e) },
        }
    }

}


pub struct KubeGetThenDeleteResponse {
    pub res: Result<(), APIError>,
}

impl View for KubeGetThenDeleteResponse {

    type V = GetThenDeleteResponse;

    open spec fn view(&self) -> GetThenDeleteResponse {
        match self.res {
            Ok(_) => GetThenDeleteResponse { res: Ok(()) },
            Err(e) => GetThenDeleteResponse { res: Err(e) },
        }
    }

}


impl View for KubeAPIResponse {

    type V = APIResponse;

    open spec fn view(&self) -> APIResponse {
        match self {
            KubeAPIResponse::GetResponse(get_resp) => APIResponse::GetResponse(get_resp@),
            KubeAPIResponse::ListResponse(list_resp) => APIResponse::ListResponse(list_resp@),
            KubeAPIResponse::CreateResponse(create_resp) => APIResponse::CreateResponse(create_resp@),
            KubeAPIResponse::DeleteResponse(delete_resp) => APIResponse::DeleteResponse(delete_resp@),
            KubeAPIResponse::UpdateResponse(update_resp) => APIResponse::UpdateResponse(update_resp@),
            KubeAPIResponse::UpdateStatusResponse(update_status_resp) => APIResponse::UpdateStatusResponse(update_status_resp@),
            KubeAPIResponse::GetThenDeleteResponse(resp) => APIResponse::GetThenDeleteResponse(resp@),
            KubeAPIResponse::GetThenUpdateResponse(resp) => APIResponse::GetThenUpdateResponse(resp@),
        }
    }

}

// File: kubernetes_api_objects/exec/api_resource.rs
#[verifier(external_body)]
pub struct ApiResource {
    inner: deps_hack::kube::api::ApiResource,
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


// File: kubernetes_api_objects/spec/api_resource.rs
pub struct ApiResourceView {
    pub kind: Kind,
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

    pub open spec fn with_generate_name(self, generate_name: StringView) -> ObjectMetaView {
        ObjectMetaView {
            generate_name: Some(generate_name),
            ..self
        }
    }

    pub open spec fn with_owner_references(self, owner_references: Seq<OwnerReferenceView>) -> ObjectMetaView {
        ObjectMetaView {
            owner_references: Some(owner_references),
            ..self
        }
    }

    pub open spec fn well_formed_for_namespaced(self) -> bool {
        &&& self.name is Some
        &&& self.namespace is Some
        &&& self.resource_version is Some
        &&& self.uid is Some
    }

}

// File: kubernetes_api_objects/exec/owner_reference.rs

implement_field_wrapper_type!(
    OwnerReference,
    deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference,
    OwnerReferenceView
);

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

// File: kubernetes_api_objects/exec/preconditions.rs

implement_field_wrapper_type!(
    Preconditions,
    deps_hack::kube::api::Preconditions,
    PreconditionsView
);


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


// File: reconciler/exec/io.rs

pub enum Request<T: View> {
    KRequest(KubeAPIRequest),
    ExternalRequest(T),
}

impl<T: View> View for Request<T> {

    type V = RequestView<T::V>;

    open spec fn view(&self) -> RequestView<T::V> {
        match self {
            Request::KRequest(req) => RequestView::KRequest(req@),
            Request::ExternalRequest(req) => RequestView::ExternalRequest(req@),
        }
    }

}


impl<T: View> DeepView for Request<T> {

   type V = RequestView<T::V>;

    open spec fn deep_view(&self) -> RequestView<T::V> {
        self@
    }

}


pub enum Response<T: View> {
    KResponse(KubeAPIResponse),
    ExternalResponse(T),
}

impl<T: View> View for Response<T> {

    type V = ResponseView<T::V>;

    open spec fn view(&self) -> ResponseView<T::V> {
        match self {
            Response::KResponse(resp) => ResponseView::KResponse(resp@),
            Response::ExternalResponse(resp) => ResponseView::ExternalResponse(resp@),
        }
    }

}


impl<T: View> DeepView for Response<T> {

    type V = ResponseView<T::V>;

    open spec fn deep_view(&self) -> ResponseView<T::V> {
        self@
    }

}


impl <T: View> Response<T> {

	#[verifier::external_body]
    pub fn is_k_response(&self) -> (res: bool)
        ensures res == self is KResponse,
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub fn as_k_response_ref(&self) -> (resp: &KubeAPIResponse)
        requires self is KResponse,
        ensures resp == self->KResponse_0,
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub fn into_k_response(self) -> (resp: KubeAPIResponse)
        requires self is KResponse,
        ensures resp == self->KResponse_0,
	{
		unimplemented!()
	}

}


pub struct VoidEReq {}

impl View for VoidEReq {

    type V = VoidEReqView;

    uninterp spec fn view(&self) -> VoidEReqView;

}


pub struct VoidEResp {}

impl View for VoidEResp {

    type V = VoidERespView;

    uninterp spec fn view(&self) -> VoidERespView;

}

pub struct VoidEReqView {}

pub struct VoidERespView {}

pub enum RequestView<T> {
    KRequest(APIRequest),
    ExternalRequest(T),
}

pub enum ResponseView<T> {
    KResponse(APIResponse),
    ExternalResponse(T),
}


// File: controllers/vreplicaset_controller/exec/reconciler.rs
pub struct VReplicaSetReconcileState {
    pub reconcile_step: VReplicaSetReconcileStep,
    pub filtered_pods: Option<Vec<Pod>>,
}

impl View for VReplicaSetReconcileState {

    type V = model_reconciler::VReplicaSetReconcileState;

    open spec fn view(&self) -> model_reconciler::VReplicaSetReconcileState {
        model_reconciler::VReplicaSetReconcileState {
            reconcile_step: self.reconcile_step@,
            filtered_pods: self.filtered_pods.deep_view(),
        }
    }

}


#[verifier::spinoff_prover]
pub fn reconcile_core(v_replica_set: &VReplicaSet, resp_o: Option<Response<VoidEResp>>, state: VReplicaSetReconcileState) -> (res: (VReplicaSetReconcileState, Option<Request<VoidEReq>>))
    requires v_replica_set@.well_formed(),
    ensures (res.0@, res.1.deep_view()) == model_reconciler::reconcile_core(v_replica_set@, resp_o.deep_view(), state@),
{
    let namespace = v_replica_set.metadata().namespace().unwrap();
    match &state.reconcile_step {
        VReplicaSetReconcileStep::Init => {
            if v_replica_set.metadata().has_deletion_timestamp() {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            } else {
                let req = KubeAPIRequest::ListRequest(KubeListRequest {
                    api_resource: Pod::api_resource(),
                    namespace: namespace,
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterListPods,
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            }
        },
        VReplicaSetReconcileStep::AfterListPods => {
            let objs = match resp_o {
		Some(Response::KResponse(KubeAPIResponse::ListResponse(KubeListResponse{ res: Ok(v) }))) => v,
                _ => { return (error_state(state), None); },
	    };
            assert(objs.deep_view() == resp_o.deep_view().unwrap()->KResponse_0->ListResponse_0.res->Ok_0);
            let pods_or_none = objects_to_pods(objs);
            if pods_or_none.is_none() {
                return (error_state(state), None);
            }
            let pods = pods_or_none.unwrap();
            let filtered_pods = filter_pods(pods, v_replica_set);
            let replicas = v_replica_set.spec().replicas().unwrap_or(0);
            if replicas < 0 {
                return (error_state(state), None);
            }
            let desired_replicas: usize = replicas as usize;
            if filtered_pods.len() == desired_replicas {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            } else if filtered_pods.len() < desired_replicas {
                let diff =  desired_replicas - filtered_pods.len();
                let pod = make_pod(v_replica_set);
                let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                    api_resource: Pod::api_resource(),
                    namespace: namespace,
                    obj: pod.marshal(),
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterCreatePod(diff - 1),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            } else {
                let diff = filtered_pods.len() - desired_replicas;
                let pod_name_or_none = filtered_pods[diff - 1].metadata().name();
                if pod_name_or_none.is_none() {
                    return (error_state(state), None);
                }
                let req = KubeAPIRequest::GetThenDeleteRequest(KubeGetThenDeleteRequest {
                    api_resource: Pod::api_resource(),
                    name: pod_name_or_none.unwrap(),
                    namespace: namespace,
                    owner_ref: v_replica_set.controller_owner_ref(),
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterDeletePod(diff - 1),
                    filtered_pods: Some(filtered_pods),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            }
        },
        VReplicaSetReconcileStep::AfterCreatePod(diff) => {
            let diff = *diff;
            match resp_o {
                Some(Response::KResponse(KubeAPIResponse::CreateResponse(KubeCreateResponse{ res: Ok(_) }))) => {},
                _ => { return (error_state(state), None); },
            }
            if diff == 0 {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            } else {
                let pod = make_pod(v_replica_set);
                let req = KubeAPIRequest::CreateRequest(KubeCreateRequest {
                    api_resource: Pod::api_resource(),
                    namespace: namespace,
                    obj: pod.marshal(),
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterCreatePod(diff - 1),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            }
        },
        VReplicaSetReconcileStep::AfterDeletePod(diff) => {
            let diff = *diff;
            match resp_o {
	        Some(Response::KResponse(KubeAPIResponse::GetThenDeleteResponse(KubeGetThenDeleteResponse{ res: Ok(_) }))) => {},
                _ => { return (error_state(state), None); },
            }
            if diff == 0 {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::Done,
                    ..state
                };
                return (state_prime, None);
            } else {
                if state.filtered_pods.is_none() {
                    return (error_state(state), None);
                }
                if diff > state.filtered_pods.as_ref().unwrap().len() {
                    return (error_state(state), None);
                }
                let pod_name_or_none = state.filtered_pods.as_ref().unwrap()[diff - 1].metadata().name();
                if pod_name_or_none.is_none() {
                    return (error_state(state), None);
                }
                let req = KubeAPIRequest::GetThenDeleteRequest(KubeGetThenDeleteRequest {
                    api_resource: Pod::api_resource(),
                    name: pod_name_or_none.unwrap(),
                    namespace: namespace,
                    owner_ref: v_replica_set.controller_owner_ref(),
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetReconcileStep::AfterDeletePod(diff - 1),
                    ..state
                };
                return (state_prime, Some(Request::KRequest(req)));
            }
        },
        _ => {
            return (state, None);
        }
    }
}

	#[verifier::external_body]
pub fn error_state(state: VReplicaSetReconcileState) -> (state_prime: VReplicaSetReconcileState)
    ensures state_prime@ == model_reconciler::error_state(state@),
	{
		unimplemented!()
	}

	#[verifier::external_body]
fn objects_to_pods(objs: Vec<DynamicObject>) -> (pods_or_none: Option<Vec<Pod>>)
    ensures pods_or_none.deep_view() == model_reconciler::objects_to_pods(objs.deep_view())
	{
		unimplemented!()
	}

	#[verifier::external_body]
fn filter_pods(pods: Vec<Pod>, v_replica_set: &VReplicaSet) -> (filtered_pods: Vec<Pod>)
    requires v_replica_set@.well_formed(),
    ensures filtered_pods.deep_view() == model_reconciler::filter_pods(pods.deep_view(), v_replica_set@),
	{
		unimplemented!()
	}

	#[verifier::external_body]
fn make_pod(v_replica_set: &VReplicaSet) -> (pod: Pod)
    requires v_replica_set@.well_formed(),
    ensures pod@ == model_reconciler::make_pod(v_replica_set@),
	{
		unimplemented!()
	}


// File: controllers/vreplicaset_controller/model/reconciler.rs
pub mod model_reconciler {
use vstd::prelude::*;
use crate::*;

pub struct VReplicaSetReconcileState {
    pub reconcile_step: VReplicaSetRecStepView,
    pub filtered_pods: Option<Seq<PodView>>,
}

pub open spec fn reconcile_core(v_replica_set: VReplicaSetView, resp_o: Option<ResponseView<VoidERespView>>, state: VReplicaSetReconcileState) -> (VReplicaSetReconcileState, Option<RequestView<VoidEReqView>>) {
    let namespace = v_replica_set.metadata.namespace.unwrap();
    match &state.reconcile_step {
        VReplicaSetRecStepView::Init => {
            if v_replica_set.metadata.deletion_timestamp is Some {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetRecStepView::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let req = APIRequest::ListRequest(ListRequest {
                    kind: PodView::kind(),
                    namespace: namespace,
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetRecStepView::AfterListPods,
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req)))
            }
        },
        VReplicaSetRecStepView::AfterListPods => {
            if !(resp_o is Some && resp_o.unwrap() is KResponse && resp_o.unwrap()->KResponse_0 is ListResponse && resp_o.unwrap()->KResponse_0->ListResponse_0.res is Ok) {
                (error_state(state), None)
            } else {
                let objs = resp_o.unwrap()->KResponse_0->ListResponse_0.res->Ok_0;
                let pods_or_none = objects_to_pods(objs);
                if pods_or_none is None {
                    (error_state(state), None)
                } else {
                    let pods = pods_or_none.unwrap();
                    let filtered_pods = filter_pods(pods, v_replica_set);
                    let replicas = v_replica_set.spec.replicas.unwrap_or(0);
                    if replicas < 0 {
                        (error_state(state), None)
                    } else {
                        let desired_replicas = replicas;
                        if filtered_pods.len() == desired_replicas {
                            let state_prime = VReplicaSetReconcileState {
                                reconcile_step: VReplicaSetRecStepView::Done,
                                ..state
                            };
                            (state_prime, None)
                        } else if filtered_pods.len() < desired_replicas {
                            let diff =  desired_replicas - filtered_pods.len();
                            let pod = make_pod(v_replica_set);
                            let req = APIRequest::CreateRequest(CreateRequest {
                                namespace: namespace,
                                obj: pod.marshal(),
                            });
                            let state_prime = VReplicaSetReconcileState {
                                reconcile_step: VReplicaSetRecStepView::AfterCreatePod((diff - 1) as nat),
                                ..state
                            };
                            (state_prime, Some(RequestView::KRequest(req)))
                        } else {
                            let diff = filtered_pods.len() - desired_replicas;
                            let pod_name_or_none = filtered_pods[diff - 1].metadata.name;
                            if pod_name_or_none is None {
                                (error_state(state), None)
                            } else {
                                let req = APIRequest::GetThenDeleteRequest(GetThenDeleteRequest {
                                    key: ObjectRef {
                                        kind: PodView::kind(),
                                        name: pod_name_or_none.unwrap(),
                                        namespace: namespace,
                                    },
                                    owner_ref: v_replica_set.controller_owner_ref(),
                                });
                                let state_prime = VReplicaSetReconcileState {
                                    reconcile_step: VReplicaSetRecStepView::AfterDeletePod((diff - 1) as nat),
                                    filtered_pods: Some(filtered_pods),
                                    ..state
                                };
                                (state_prime, Some(RequestView::KRequest(req)))
                            }
                        }
                    }
                }
            }
        },
        VReplicaSetRecStepView::AfterCreatePod(diff) => {
            let diff = *diff;
            if !(resp_o is Some && resp_o.unwrap() is KResponse && resp_o.unwrap()->KResponse_0 is CreateResponse
                 && resp_o.unwrap()->KResponse_0->CreateResponse_0.res is Ok) {
                (error_state(state), None)
            } else if diff == 0 {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetRecStepView::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                let pod = make_pod(v_replica_set);
                let req = APIRequest::CreateRequest(CreateRequest {
                    namespace: namespace,
                    obj: pod.marshal(),
                });
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetRecStepView::AfterCreatePod((diff - 1) as nat),
                    ..state
                };
                (state_prime, Some(RequestView::KRequest(req)))
            }
        },
        VReplicaSetRecStepView::AfterDeletePod(diff) => {
            let diff = *diff;
            if !(resp_o is Some && resp_o.unwrap() is KResponse && resp_o.unwrap()->KResponse_0 is GetThenDeleteResponse
                 && resp_o.unwrap()->KResponse_0->GetThenDeleteResponse_0.res is Ok) {
                (error_state(state), None)
            } else if diff == 0 {
                let state_prime = VReplicaSetReconcileState {
                    reconcile_step: VReplicaSetRecStepView::Done,
                    ..state
                };
                (state_prime, None)
            } else {
                if state.filtered_pods is None {
                    (error_state(state), None)
                } else if diff > state.filtered_pods.unwrap().len() {
                    (error_state(state), None)
                } else {
                    let pod_name_or_none = state.filtered_pods.unwrap()[diff - 1].metadata.name;
                    if pod_name_or_none is None {
                        (error_state(state), None)
                    } else {
                        let req = APIRequest::GetThenDeleteRequest(GetThenDeleteRequest {
                            key: ObjectRef {
                                kind: PodView::kind(),
                                name: pod_name_or_none.unwrap(),
                                namespace: namespace,
                            },
                            owner_ref: v_replica_set.controller_owner_ref(),
                        });
                        let state_prime = VReplicaSetReconcileState {
                            reconcile_step: VReplicaSetRecStepView::AfterDeletePod((diff - 1) as nat),
                            ..state
                        };
                        (state_prime, Some(RequestView::KRequest(req)))
                    }
                }
            }
        },
        _ => {
            (state, None)
        }
    }
}

pub open spec fn error_state(state: VReplicaSetReconcileState) -> (state_prime: VReplicaSetReconcileState)
{
    VReplicaSetReconcileState {
        reconcile_step: VReplicaSetRecStepView::Error,
        ..state
    }
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

pub open spec fn make_pod(v_replica_set: VReplicaSetView) -> (pod: PodView) {
    let template = v_replica_set.spec.template.unwrap();
    let pod = PodView::default();
    let pod = PodView {
        spec: template.spec,
        metadata: {
            let tm = template.metadata.unwrap();
            let metadata = ObjectMetaView::default();
            let metadata = ObjectMetaView {
                labels: tm.labels,
                annotations: tm.annotations,
                finalizers: tm.finalizers,
                ..metadata
            };
            let metadata = metadata.with_generate_name(
                v_replica_set.metadata.name.unwrap() + "-"@
            );
            let metadata = metadata.with_owner_references(
                make_owner_references(v_replica_set)
            );
            metadata
        },
        ..pod
    };
    pod
}

pub open spec fn make_owner_references(v_replica_set: VReplicaSetView) -> Seq<OwnerReferenceView> { seq![v_replica_set.controller_owner_ref()] }
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

    pub open spec fn well_formed(self) -> bool {
        &&& self.metadata.well_formed_for_namespaced()
        &&& self.state_validation()
    }

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
pub enum VReplicaSetReconcileStep {
    Init,
    AfterListPods,
    AfterCreatePod(usize),
    AfterDeletePod(usize),
    Done,
    Error,
}

impl View for VReplicaSetReconcileStep {

    type V = VReplicaSetRecStepView;

    open spec fn view(&self) -> VReplicaSetRecStepView {
        match self {
            VReplicaSetReconcileStep::Init => VReplicaSetRecStepView::Init,
            VReplicaSetReconcileStep::AfterListPods => VReplicaSetRecStepView::AfterListPods,
            VReplicaSetReconcileStep::AfterCreatePod(diff) => VReplicaSetRecStepView::AfterCreatePod(*diff as nat),
            VReplicaSetReconcileStep::AfterDeletePod(diff) => VReplicaSetRecStepView::AfterDeletePod(*diff as nat),
            VReplicaSetReconcileStep::Done => VReplicaSetRecStepView::Done,
            VReplicaSetReconcileStep::Error => VReplicaSetRecStepView::Error,
        }
    }

}


pub enum VReplicaSetRecStepView {
    Init,
    AfterListPods,
    AfterCreatePod(nat),
    AfterDeletePod(nat),
    Done,
    Error,
}


// File: kubernetes_api_objects/error.rs
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


// File: kubernetes_api_objects/exec/object_meta.rs
impl ObjectMeta {

	#[verifier::external_body]
    #[verifier(external_body)]
    pub fn name(&self) -> (name: Option<String>)
        ensures self@.name == name.deep_view()
	{
		unimplemented!()
	}

	#[verifier::external_body]
    #[verifier(external_body)]
    pub fn namespace(&self) -> (namespace: Option<String>)
        ensures self@.namespace == namespace.deep_view()
	{
		unimplemented!()
	}

	#[verifier::external_body]
    #[verifier(external_body)]
    pub fn has_deletion_timestamp(&self) -> (b: bool)
        ensures b == self@.deletion_timestamp is Some,
	{
		unimplemented!()
	}

}




// File: controllers/vreplicaset_controller/trusted/exec_types.rs
implement_object_wrapper_type!(
    VReplicaSet,
    deps_hack::VReplicaSet,
    /*spec_types::*/VReplicaSetView
);

implement_field_wrapper_type!(
    VReplicaSetSpec,
    deps_hack::VReplicaSetSpec,
    /*spec_types::*/VReplicaSetSpecView
);

impl VReplicaSet {

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: VReplicaSetSpec)
        ensures spec@ == self@.spec,
	{
		unimplemented!()
	}

    #[verifier(external_body)]
    pub fn controller_owner_ref(&self) -> (owner_reference: OwnerReference)
        ensures owner_reference@ == self@.controller_owner_ref(),
	{
		unimplemented!()
	}

}


impl VReplicaSetSpec {

    #[verifier(external_body)]
    pub fn replicas(&self) -> (replicas: Option<i32>)
        ensures
            replicas is Some == self@.replicas is Some,
            replicas is Some ==> replicas->0 as int == self@.replicas->0,
	{
		unimplemented!()
	}

}
}


