# Copyright (c) Microsoft Corporation. #
# Licensed under the MIT license.      #


import openai
from openai import AzureOpenAI, OpenAI
import time
import random


class LLM:
    def __init__(self, config, logger):
        self.config = config
        self.logger = logger
        self.client = []
        if config.use_openai:
            for i in range(len(config.aoai_api_key)):
                self.client.append(
                    OpenAI(
                        api_key=config.aoai_api_key[i],
                        base_url=config.aoai_api_base[i],
                        max_retries=config.aoai_max_retries,
                    )
                )
        # there may be no key and instead authentication is used
        elif len(config.aoai_api_key) == 0:
            from azure.identity import DefaultAzureCredential, get_bearer_token_provider

            token_provider = get_bearer_token_provider(
                DefaultAzureCredential(), "https://cognitiveservices.azure.com/.default"
            )
            self.client.append(
                AzureOpenAI(
                    azure_ad_token_provider=token_provider,
                    azure_endpoint=config.aoai_api_base[0],
                    api_version=config.aoai_api_version,
                    max_retries=config.aoai_max_retries,
                )
            )
        else:
            for i in range(len(config.aoai_api_key)):
                self.client.append(
                    AzureOpenAI(
                        api_key=config.aoai_api_key[i],
                        azure_endpoint=config.aoai_api_base[i],
                        api_version=config.aoai_api_version,
                        max_retries=config.aoai_max_retries,
                    )
                )
        self.client_id = random.randint(0, len(self.client) - 1)

    def _add_client_id(self):
        self.client_id += 1
        self.client_id %= len(self.client)

    def _reset_client_id(self):
        if len(self.client) == 1:
            return
        self.client_id += random.randint(1, len(self.client) - 1)
        self.client_id %= len(self.client)

    def infer_llm(
        self,
        engine,
        instruction,
        exemplars,
        query,
        system_info=None,
        answer_num=1,
        max_tokens=2048,
        temp=0.7,
        json=False,
        return_msg=False,
        verbose=False,
    ):
        """
        Args:
            instruction: str
            exemplars: list of dict {"query": str, "answer": str}
            query: str
        Returns:
            answers: list of str
        """
        self._reset_client_id()
        # self.client_id = 0
        if verbose:
            self.logger.info(f"Using client {self.client_id}")

        system_info = (
            "You are a helpful AI assistant." if system_info is None else system_info
        )
        messages = [{"role": "system", "content": system_info}]
        if instruction is not None:
            messages.append({"role": "user", "content": instruction})
            messages.append({"role": "assistant", "content": "OK, I'm ready to help."})

        if exemplars is not None:
            for i, exemplar in enumerate(exemplars):
                messages.append({"role": "user", "content": exemplar["query"]})
                messages.append({"role": "assistant", "content": exemplar["answer"]})

        messages.append({"role": "user", "content": query})

        # engine in ["gpt-35-turbo", "gpt-4"]

        # for m in messages:
        #     self.logger.info(f"{m['role']}: {m['content']}")

        cur_time = time.time()
        while True:
            try:
                answers = self.client[self.client_id].chat.completions.create(
                    model=engine,
                    messages=messages,
                    temperature=temp,
                    max_tokens=max_tokens,
                    top_p=1.0,
                    n=answer_num,
                    frequency_penalty=0,
                    presence_penalty=0,
                    stop=None,
                    response_format={"type": "json_object" if json else "text"},
                )
                break
            except openai.NotFoundError as e:
                self._add_client_id()
                continue
            except openai.BadRequestError as e:
                if return_msg:
                    return [], messages
                else:
                    return []
            except openai.RateLimitError:
                if len(self.client) == 1:
                    print("Rate Limit Error")
                    time.sleep(10)
                else:
                    self._add_client_id()
                continue
        self.logger.info(f"Infer time: {time.time() - cur_time}s")
        if return_msg:
            return [
                response.message.content if response.finish_reason != "length" else ""
                for response in answers.choices
            ], messages
        else:
            return [
                response.message.content if response.finish_reason != "length" else ""
                for response in answers.choices
            ]

    def infer_llm_with_history(
        self,
        engine,
        history,
        query,
        answer_num=1,
        max_tokens=2048,
        temp=0.7,
        json=False,
        return_msg=False,
        verbose=False,
    ):
        """
        Args:
            instruction: str
            history: List
            query: str
        Returns:
            answers: list of str
        """
        self._reset_client_id()
        # self.client_id = 0
        if verbose:
            self.logger.info(f"Using client {self.client_id}")

        messages = history[:]
        messages.append({"role": "user", "content": query})

        while True:
            try:
                answers = self.client[self.client_id].chat.completions.create(
                    model=engine,
                    messages=messages,
                    temperature=temp,
                    max_tokens=max_tokens,
                    top_p=1.0,
                    n=answer_num,
                    frequency_penalty=0,
                    presence_penalty=0,
                    stop=None,
                    response_format={"type": "json_object" if json else "text"},
                )
                break
            except openai.NotFoundError:
                self._add_client_id()
                continue
            except openai.BadRequestError:
                if return_msg:
                    return [], messages
                else:
                    return []
            except openai.RateLimitError:
                if len(self.client) == 1:
                    time.sleep(10)
                else:
                    self._add_client_id()
                continue
        if return_msg:
            return [
                response.message.content if response.finish_reason != "length" else ""
                for response in answers.choices
            ], messages
        else:
            return [
                response.message.content if response.finish_reason != "length" else ""
                for response in answers.choices
            ]
