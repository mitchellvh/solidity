/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsolidity/analysis/ControlFlowGraph.h>

#include <libsolidity/analysis/ControlFlowBuilder.h>

using namespace std;
using namespace solidity::langutil;
using namespace solidity::frontend;

bool CFG::constructFlow(ASTNode const& _astRoot)
{
	_astRoot.accept(*this);
	return !Error::containsErrors(m_errorReporter.errors());
}


bool CFG::visit(FunctionDefinition const& _function)
{
	if (_function.isImplemented() && _function.isFree())
		m_functionControlFlow[{nullptr, &_function}] = ControlFlowBuilder::createFunctionFlow(m_nodeContainer, _function);
	return false;
}

bool CFG::visit(ContractDefinition const& _contract)
{
	for (ContractDefinition const* contract: _contract.annotation().linearizedBaseContracts)
	{
		for (FunctionDefinition const* function: contract->definedFunctions())
			if (function->isImplemented())
			{
				// TODO read used modifiers from function flow and create flows
				// for only those


				//auto const& flow =
					m_functionControlFlow[{&_contract, function}] =
					ControlFlowBuilder::createFunctionFlow(m_nodeContainer, *function);

	/*	snipped for resolving modifiers
	 *	for (auto const& modifierInvocation: flow->modifierInvocations)
				{
				}
	auto modifierDefinition = dynamic_cast<ModifierDefinition const*>(
		_modifierInvocation.name().annotation().referencedDeclaration
	);
	if (!modifierDefinition) return false;
	if (!modifierDefinition->isImplemented()) return false;
*/
			}
		for (ModifierDefinition const* modifier: contract->functionModifiers())
			if (modifier->isImplemented())
				m_functionControlFlow[{&_contract, modifier}] =
					ControlFlowBuilder::createFunctionFlow(m_nodeContainer, *modifier);
	}

	return true;
}

FunctionFlow const& CFG::functionFlow(CallableDeclaration const& _callable, ContractDefinition const* _contract) const
{
	return *m_functionControlFlow.at({_contract, &_callable});
}

CFGNode* CFG::NodeContainer::newNode()
{
	m_nodes.emplace_back(std::make_unique<CFGNode>());
	return m_nodes.back().get();
}
